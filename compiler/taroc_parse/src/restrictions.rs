use super::package::Parser;

bitflags::bitflags! {
    #[derive(Clone, Copy, Debug)]
    pub struct Restrictions: u8 {
        const ALLOW_BINDING_CONDITION = 1 << 0;
        const ALLOW_WILDCARD = 1 << 1;
        const ALLOW_REST_PATTERN = 1 << 2;
        const NO_STRUCT_LITERALS = 1 << 3;
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
