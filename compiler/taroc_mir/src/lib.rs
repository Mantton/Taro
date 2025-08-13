use index_vec::IndexVec;

pub struct Body {
    pub blocks: Blocks,
}

pub struct Blocks {
    blocks: IndexVec<BlockID, BlockData>,
}

index_vec::define_index_type! {
    pub struct BlockID = u32;
}

pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

pub struct Statement {
    pub kind: StatementKind,
}

pub enum StatementKind {
    Assign { destination: Place, source: RValue },
    SetDiscriminant { place: Place, variant_index: u32 },
    NOP,
}

pub struct Terminator {
    pub kind: TerminatorKind,
}

pub enum TerminatorKind {
    Goto {
        target: BlockID,
    },
    SwitchInt {
        discrimimant: Operand,
        targets: SwitchTargets,
    },
    Return,
    Unreachable,
    Call {
        func: Operand,
        arguments: Vec<Operand>,
        destination: Place,
        target: BlockID,
        source: CallSource,
    },
}

pub enum CallSource {
    Normal,
    Operator,
}

pub struct SwitchTargets {
    values: Vec<u64>,
    targets: Vec<BlockID>,
}

index_vec::define_index_type! {
    pub struct LocalID = u32;
}

// Represents 'where' a value lives
// A Location you can read from or write to
// e.g local, field, index
pub struct Place {
    local: LocalID,
    path: Vec<PlaceSource>,
}

pub enum PlaceSource {
    Dereference,
    Field,
    Index,
}

// Represents 'what' an operation consumes,
// A 'by-value input
pub enum Operand {
    Use(Place), // 'Using' a Place Reads its Value
    Constant,
}

// Represents how to produce a value
// A computation or constructor that yields a value (NOT a location/place)
// They are build from Operands or refernce to a place
pub enum RValue {
    Use(Operand),
    AddressOf(Place),
    BinaryOp(u8, Operand, Operand),
    UnaryOp(u8, Operand),
    Cast,
    Discriminant(Place),
}
