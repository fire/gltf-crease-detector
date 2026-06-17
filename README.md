# gltf-crease-detector

Lean-side GLB mesh crease oracle.

Input is a `.glb`. The checker reads embedded glTF JSON/BIN data, evaluates all
skinned mesh nodes/primitives affected by animation, then reports edge dihedral
creases grouped by dominant joint/node pair.

## Usage

```bash
lake exe gltf-crease-detector /path/to/model.glb
```
