import Lake
open Lake DSL

package «gltf-crease-detector» where

require «lean-gltf» from git
  "https://github.com/fire/lean-gltf" @ "main"

lean_lib GltfCreaseDector where
  globs := #[.submodules `GltfCreaseDector]

@[default_target]
lean_exe «gltf-crease-detector» where
  root := `GltfCreaseDector.Cli
