use std::ops::Add;

index_vec::define_index_type! {
    pub struct PackageIndex = u32;
}

impl PackageIndex {
    pub const LOCAL: PackageIndex = PackageIndex { _raw: 0 };
}
