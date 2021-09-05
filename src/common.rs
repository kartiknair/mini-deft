pub type Span = std::ops::Range<usize>;

#[derive(Debug, Clone)]
pub struct Error {
    pub message: String,
    pub span: Span,
}
