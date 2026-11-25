use zed::{
    LanguageServerId, Worktree,
    settings::{CommandSettings, LspSettings},
};
use zed_extension_api as zed;

struct Taro;

impl zed::Extension for Taro {
    fn new() -> Self {
        Self
    }

    fn language_server_command(
        &mut self,
        server: &LanguageServerId,
        worktree: &Worktree,
    ) -> zed::Result<zed::Command> {
        let binary = LspSettings::for_worktree(server.as_ref(), worktree)?
            .binary
            .unwrap_or(CommandSettings {
                path: None,
                arguments: None,
                env: None,
            });
        let command = binary
            .path
            .or_else(|| worktree.which("taro-lsp"))
            .ok_or("taro-lsp was not found. Set lsp.taro-lsp.binary.path or add it to PATH.")?;
        Ok(zed::Command {
            command,
            args: binary.arguments.unwrap_or_default(),
            env: binary.env.unwrap_or_default().into_iter().collect(),
        })
    }
}

zed::register_extension!(Taro);
