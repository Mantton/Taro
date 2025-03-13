use std::{env, path::PathBuf};
use taroc_constants::{LANGUAGE_HOME, PACKAGE_SOURCE, PACKAGE_STORE};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PackageIdentifier {
    pub name: String,
}

impl From<String> for PackageIdentifier {
    fn from(value: String) -> Self {
        Self { name: value }
    }
}

impl PackageIdentifier {
    pub fn segments(&self) -> Vec<String> {
        let base = self
            .name
            .strip_prefix("https://")
            .or_else(|| self.name.strip_prefix("http://"))
            .unwrap_or(&self.name);

        let segments: Vec<&str> = base.split("/").collect();
        segments.iter().map(|v| v.to_string()).collect()
    }

    pub fn source_path(&self) -> Result<PathBuf, String> {
        let mut source = env::var(LANGUAGE_HOME)
            .map(|home| PathBuf::from(home).join(PACKAGE_SOURCE))
            .map_err(|err| format!("{} `{}`", err, LANGUAGE_HOME))?;

        // Subs
        let segments = self.segments();
        for sub in segments.iter() {
            source.push(sub)
        }

        Ok(source)
    }

    pub fn install_path(&self, revision: String) -> Result<PathBuf, String> {
        let mut store = env::var(LANGUAGE_HOME)
            .map(|home| PathBuf::from(home).join(PACKAGE_STORE))
            .map_err(|err| format!("{} `{}`", err, LANGUAGE_HOME))?;

        // Subs
        let segments = self.segments();
        for (index, sub) in segments.iter().enumerate() {
            if index == segments.len() - 1 {
                store.push(format!("{}@{}", sub, revision));
            } else {
                store.push(sub)
            }
        }

        Ok(store)
    }

    pub fn source_repository(&self) -> String {
        if self.name.starts_with("http") {
            self.name.clone()
        } else {
            format!("https://{}", self.name)
        }
    }

    pub fn normalized(value: &String) -> String {
        // remove trailing slash & leading scheme
        let mut value = value
            .strip_prefix("https://")
            .or_else(|| value.strip_prefix("http://"))
            .unwrap_or(&value);

        value = value.strip_suffix("/").unwrap_or(&value);
        value.into()
    }

    pub fn normalize(&self) -> String {
        Self::normalized(&self.name)
    }

    pub fn alias(&self) -> String {
        self.segments().last().unwrap().clone()
    }
}
