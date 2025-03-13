use super::package::Parser;

bitflags::bitflags! {
    #[derive(Clone, Copy, Debug)]
    pub struct Restrictions: u8 {
        const ALLOW_BLOCK_EXPRESSION = 1 << 1;
        const ALLOW_BINDING_CONDITION = 1 << 2;
        const ALLOW_WILDCARD = 1 << 3;
        const NO_TRAILING_CLOSURES = 1 << 4;
        const ALLOW_REST_PATTERN = 1 << 5;
    }
}

impl Parser {
    pub fn with_restrictions<T>(&mut self, res: Restrictions, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.restrictions.clone();
        self.restrictions = res;
        let res = f(self);
        self.restrictions = old;
        res
    }
}
