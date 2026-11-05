use super::*;
use crate::{sync::SyncState, test_layout};

#[test]
fn raced_rejection_leaves_the_source_intact_and_receipt_preserves_the_copy() {
    let layout = unsafe { ChannelLayout::new(test_layout::value::<u64>()) }.unwrap();
    let mut state = SyncState::default();
    let channel = state.channel_create_with_layout(layout.clone(), 1, true);
    let first = 41_u64;
    let second = 42_u64;
    let staged = unsafe { QueuedValue::prepare(&layout, (&raw const first).cast()) }.unwrap();
    assert_eq!(state.channel_try_send_value(channel, staged).0, 0);
    let staged = unsafe { QueuedValue::prepare(&layout, (&raw const second).cast()) }.unwrap();
    let (status, _, rejected) = state.channel_try_send_value(channel, staged);
    assert_eq!(status, super::super::err_would_block());
    drop(rejected);
    assert_eq!(second, 42);
    let mut output = 0_u64;
    let (status, _, received) = state.channel_try_recv(channel, (&raw mut output).cast());
    assert_eq!(status, 0);
    drop(received);
    assert_eq!(output, first);
    assert_eq!(first, 41);
}

#[test]
fn zero_sized_messages_need_no_source_or_destination_bytes() {
    let layout = unsafe { ChannelLayout::new(test_layout::value::<()>()) }.unwrap();
    let mut value = unsafe { QueuedValue::prepare(&layout, std::ptr::null()) }.unwrap();
    value.commit();
    unsafe { value.move_into(std::ptr::null_mut()) };
}

#[test]
fn staging_roots_the_source_before_its_first_allocation_and_releases_abandoned_copies() {
    use crate::{
        garbage_collector as gc,
        test_layout::{BYTE, POINTER, POINTER_VALUE},
    };
    std::thread::spawn(|| unsafe {
        gc::__gc__thread_enter_managed();
        let layout = ChannelLayout::new(&POINTER_VALUE).unwrap();
        let source = gc::__gc__alloc(1, &BYTE);
        source.write(42);
        let probe = gc::with_runtime_root((&raw const source).cast(), &POINTER, || {
            gc::create_weak_cell(source)
        });
        gc::with_runtime_root((&raw const probe).cast(), &POINTER, || {
            gc::__gc__test_request_collection();
            let staged = QueuedValue::prepare(&layout, (&raw const source).cast()).unwrap();
            gc::__gc__collect();
            assert!(!crate::gc_weak::load_cell(probe).is_null());
            assert_eq!(source.read(), 42);
            drop(staged);
            gc::__gc__collect();
            assert!(crate::gc_weak::load_cell(probe).is_null());
        });
        gc::__gc__thread_detach();
    })
    .join()
    .unwrap();
}
