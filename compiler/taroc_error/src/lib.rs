#[derive(Debug)]
pub enum CompileError {
    Reported,
    Message(String),
}

pub type CompileResult<T> = Result<T, CompileError>;
