use crate::sema::resolve::models::ScopeData;

#[derive(Default)]
pub struct ResolverArenas {
    pub bump: bumpalo::Bump,
}
