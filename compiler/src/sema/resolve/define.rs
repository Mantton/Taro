use crate::sema::resolve::resolver::Resolver;

pub struct Actor<'resolver> {
    resolver: &'resolver Resolver,
}

impl<'r> Actor<'r> {
    fn new(resolver: &'r Resolver) -> Actor<'r> {
        Actor { resolver }
    }
}
