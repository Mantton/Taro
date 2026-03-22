use zed_extension_api::{
    self as zed, Command, Extension, LanguageServerId, Result as ZedResult, Worktree,
};

struct TaroExtension;

impl Extension for TaroExtension {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        _worktree: &Worktree,
    ) -> ZedResult<Command> {
        Ok(Command {
            command: "taro-lsp".into(),
            args: vec![],
            env: vec![],
        })
    }
}

zed::register_extension!(TaroExtension);
