import Lean
import LeanGltf

open Lean

namespace GltfCreaseDector

abbrev Mat4 := Array Float

structure BufferView where
  buffer : Nat := 0
  byteOffset : Nat := 0
  byteLength : Nat := 0
  byteStride : Option Nat := none
  deriving Inhabited, Repr

structure Accessor where
  bufferView : Option Nat := none
  byteOffset : Nat := 0
  componentType : Nat := 0
  count : Nat := 0
  typeName : String := "SCALAR"
  deriving Inhabited, Repr

structure Primitive where
  position : Nat
  joints : Option Nat := none
  weights : Option Nat := none
  indices : Option Nat := none
  deriving Inhabited, Repr

structure Mesh where
  name : String := ""
  primitives : Array Primitive := #[]
  deriving Inhabited, Repr

structure Skin where
  joints : Array Nat := #[]
  inverseBindMatrices : Option Nat := none
  deriving Inhabited, Repr

structure Node where
  name : String := ""
  mesh : Option Nat := none
  skin : Option Nat := none
  children : Array Nat := #[]
  translation : Array Float := #[0,0,0]
  rotation : Array Float := #[0,0,0,1]
  scale : Array Float := #[1,1,1]
  deriving Inhabited, Repr

structure AnimSampler where
  input : Nat
  output : Nat
  deriving Inhabited, Repr

structure AnimChannel where
  sampler : Nat
  targetNode : Nat
  path : String
  deriving Inhabited, Repr

structure Animation where
  samplers : Array AnimSampler := #[]
  channels : Array AnimChannel := #[]
  deriving Inhabited, Repr

structure Glb where
  json : Json
  bin : ByteArray
  bufferViews : Array BufferView
  accessors : Array Accessor
  meshes : Array Mesh
  skins : Array Skin
  nodes : Array Node
  animations : Array Animation
  deriving Inhabited

private def mat4Identity : Mat4 :=
  #[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]

private def mat4Mul (a b : Mat4) : Mat4 := Id.run do
  let mut r : Array Float := Array.mkEmpty 16
  for j in [:4] do
    for i in [:4] do
      let mut s : Float := 0
      for k in [:4] do s := s + a[k*4+i]! * b[j*4+k]!
      r := r.push s
  pure r

private def mat4FromTRS (tx ty tz qx qy qz qw sx sy sz : Float) : Mat4 :=
  let xx := qx*qx; let yy := qy*qy; let zz := qz*qz
  let xy := qx*qy; let xz := qx*qz; let yz := qy*qz
  let wx := qw*qx; let wy := qw*qy; let wz := qw*qz
  let r00 := 1.0 - 2.0*(yy+zz); let r01 := 2.0*(xy-wz); let r02 := 2.0*(xz+wy)
  let r10 := 2.0*(xy+wz); let r11 := 1.0 - 2.0*(xx+zz); let r12 := 2.0*(yz-wx)
  let r20 := 2.0*(xz-wy); let r21 := 2.0*(yz+wx); let r22 := 1.0 - 2.0*(xx+yy)
  #[r00*sx,r10*sx,r20*sx,0, r01*sy,r11*sy,r21*sy,0, r02*sz,r12*sz,r22*sz,0, tx,ty,tz,1]

private def transformPoint (m : Mat4) (p : Float × Float × Float) : Float × Float × Float :=
  let x := p.1; let y := p.2.1; let z := p.2.2
  (m[0]!*x + m[4]!*y + m[8]!*z + m[12]!,
   m[1]!*x + m[5]!*y + m[9]!*z + m[13]!,
   m[2]!*x + m[6]!*y + m[10]!*z + m[14]!)

private def add3 (a b : Float × Float × Float) := (a.1+b.1, a.2.1+b.2.1, a.2.2+b.2.2)
private def sub3 (a b : Float × Float × Float) := (a.1-b.1, a.2.1-b.2.1, a.2.2-b.2.2)
private def scale3 (s : Float) (a : Float × Float × Float) := (s*a.1, s*a.2.1, s*a.2.2)
private def dot3 (a b : Float × Float × Float) := a.1*b.1 + a.2.1*b.2.1 + a.2.2*b.2.2
private def cross3 (a b : Float × Float × Float) :=
  (a.2.1*b.2.2 - a.2.2*b.2.1, a.2.2*b.1 - a.1*b.2.2, a.1*b.2.1 - a.2.1*b.1)
private def norm3 (a : Float × Float × Float) := Float.sqrt (dot3 a a)
private def normalize3 (a : Float × Float × Float) := let n := norm3 a; if n > 1e-7 then scale3 (1.0/n) a else (0,0,1)
private def angleDeg (a b : Float × Float × Float) :=
  let d0 := dot3 a b; let d := if d0 < -1 then -1 else if d0 > 1 then 1 else d0
  Float.acos d * 57.29577951308232

private def leU32 (b : ByteArray) (o : Nat) : UInt32 :=
  (b[o]!.toUInt32) ||| (b[o+1]!.toUInt32 <<< 8) ||| (b[o+2]!.toUInt32 <<< 16) ||| (b[o+3]!.toUInt32 <<< 24)

private def leU16 (b : ByteArray) (o : Nat) : Nat := b[o]!.toNat ||| (b[o+1]!.toNat <<< 8)

private def pow2 (e : Int) : Float := Id.run do
  let mut out := 1.0
  if e >= 0 then for _ in [:e.toNat] do out := out * 2.0 else for _ in [:(-e).toNat] do out := out / 2.0
  pure out

private def f32 (bits : UInt32) : Float :=
  let sign := if (bits &&& 0x80000000) == 0 then 1.0 else -1.0
  let exp := ((bits >>> 23) &&& 0xff).toNat
  let mant := (bits &&& 0x7fffff).toNat
  if exp == 0 then sign * (Float.ofNat mant / 8388608.0) * pow2 (-126)
  else if exp == 255 then 0.0
  else sign * (1.0 + Float.ofNat mant / 8388608.0) * pow2 (Int.ofNat exp - 127)

private def leF32 (b : ByteArray) (o : Nat) : Float := f32 (leU32 b o)

private def jsonArr (j : Json) (k : String) : Array Json :=
  match j.getObjVal? k >>= (·.getArr?) with | .ok a => a | .error _ => #[]
private def jsonObj? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with | .ok x => some x | .error _ => none
private def jsonNat? (j : Json) (k : String) : Option Nat :=
  match j.getObjVal? k >>= (·.getNat?) with | .ok n => some n | .error _ => none
private def jsonStr? (j : Json) (k : String) : Option String :=
  match j.getObjVal? k >>= (·.getStr?) with | .ok s => some s | .error _ => none
private def jsonNatArr (j : Json) (k : String) : Array Nat :=
  (jsonArr j k).filterMap (fun x => match x.getNat? with | .ok n => some n | .error _ => none)

private def pow10Inv (n : Nat) : Float := Id.run do
  let mut out := 1.0
  for _ in [:n] do out := out / 10.0
  pure out

private def jsonFloat? (j : Json) : Option Float :=
  match j.getNum? with
  | .ok n => some (Float.ofInt n.mantissa * pow10Inv n.exponent)
  | .error _ => none

private def jsonFloatArr (j : Json) (k : String) : Array Float :=
  (jsonArr j k).filterMap jsonFloat?

private def parseBufferView (j : Json) : BufferView :=
  { buffer := (jsonNat? j "buffer").getD 0, byteOffset := (jsonNat? j "byteOffset").getD 0,
    byteLength := (jsonNat? j "byteLength").getD 0, byteStride := jsonNat? j "byteStride" }
private def parseAccessor (j : Json) : Accessor :=
  { bufferView := jsonNat? j "bufferView", byteOffset := (jsonNat? j "byteOffset").getD 0,
    componentType := (jsonNat? j "componentType").getD 0, count := (jsonNat? j "count").getD 0,
    typeName := (jsonStr? j "type").getD "SCALAR" }
private def parsePrimitive (j : Json) : Option Primitive := do
  let attrs ← jsonObj? j "attributes"
  let pos ← jsonNat? attrs "POSITION"
  some { position := pos, joints := jsonNat? attrs "JOINTS_0", weights := jsonNat? attrs "WEIGHTS_0", indices := jsonNat? j "indices" }
private def parseMesh (j : Json) : Mesh :=
  { name := (jsonStr? j "name").getD "", primitives := (jsonArr j "primitives").filterMap parsePrimitive }
private def parseSkin (j : Json) : Skin :=
  { joints := jsonNatArr j "joints", inverseBindMatrices := jsonNat? j "inverseBindMatrices" }
private def parseNode (j : Json) : Node :=
  { name := (jsonStr? j "name").getD "", mesh := jsonNat? j "mesh", skin := jsonNat? j "skin",
    children := jsonNatArr j "children", translation := let a := jsonFloatArr j "translation"; if a.size == 3 then a else #[0,0,0],
    rotation := let a := jsonFloatArr j "rotation"; if a.size == 4 then a else #[0,0,0,1],
    scale := let a := jsonFloatArr j "scale"; if a.size == 3 then a else #[1,1,1] }
private def parseSampler (j : Json) : Option AnimSampler := do some { input := (← jsonNat? j "input"), output := (← jsonNat? j "output") }
private def parseChannel (j : Json) : Option AnimChannel := do
  let target ← jsonObj? j "target"; some { sampler := (← jsonNat? j "sampler"), targetNode := (← jsonNat? target "node"), path := (jsonStr? target "path").getD "" }
private def parseAnimation (j : Json) : Animation :=
  { samplers := (jsonArr j "samplers").filterMap parseSampler, channels := (jsonArr j "channels").filterMap parseChannel }

private def utf8String (b : ByteArray) : String := String.fromUTF8! b

private def parseGlb (path : System.FilePath) : IO Glb := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size < 20 || leU32 bytes 0 != 0x46546c67 then throw <| IO.userError "not a GLB"
  let jsonLen := (leU32 bytes 12).toNat
  let jsonType := leU32 bytes 16
  if jsonType != 0x4e4f534a then throw <| IO.userError "missing JSON chunk"
  let jsonBytes := bytes.extract 20 (20+jsonLen)
  let json ← match Json.parse (utf8String jsonBytes) with | .ok j => pure j | .error e => throw <| IO.userError e
  let binStart0 := 20 + jsonLen
  let bin :=
    if binStart0 + 8 <= bytes.size then
      let len := (leU32 bytes binStart0).toNat
      let typ := leU32 bytes (binStart0+4)
      if typ == 0x004e4942 then bytes.extract (binStart0+8) (binStart0+8+len) else ByteArray.empty
    else ByteArray.empty
  let bufferViews := (jsonArr json "bufferViews").map parseBufferView
  let accessors := (jsonArr json "accessors").map parseAccessor
  let meshes := (jsonArr json "meshes").map parseMesh
  let skins := (jsonArr json "skins").map parseSkin
  let nodes := (jsonArr json "nodes").map parseNode
  let animations := (jsonArr json "animations").map parseAnimation
  pure (Glb.mk json bin bufferViews accessors meshes skins nodes animations)

private def comps (ty : String) : Nat := if ty == "SCALAR" then 1 else if ty == "VEC2" then 2 else if ty == "VEC3" then 3 else if ty == "VEC4" then 4 else if ty == "MAT4" then 16 else 1
private def compSize (ct : Nat) : Nat := if ct == 5126 || ct == 5125 then 4 else if ct == 5123 then 2 else 1
private def accessorOffset (g : Glb) (ai : Nat) : Nat × Nat :=
  let a := g.accessors[ai]!
  match a.bufferView with
  | none => (a.byteOffset, comps a.typeName * compSize a.componentType)
  | some bvIdx =>
    let bv := g.bufferViews[bvIdx]!
    let stride := bv.byteStride.getD (comps a.typeName * compSize a.componentType)
    (bv.byteOffset + a.byteOffset, stride)

private def readFloatAccessor (g : Glb) (ai : Nat) : Array Float := Id.run do
  let a := g.accessors[ai]!
  let n := comps a.typeName
  let (base, stride) := accessorOffset g ai
  let mut out := Array.mkEmpty (a.count*n)
  for i in [:a.count] do
    let row := base + i*stride
    for k in [:n] do out := out.push (leF32 g.bin (row + 4*k))
  pure out

private def readIndexAccessor (g : Glb) (ai : Nat) : Array Nat := Id.run do
  let a := g.accessors[ai]!
  let (base, stride) := accessorOffset g ai
  let mut out := Array.mkEmpty a.count
  for i in [:a.count] do
    let off := base + i*stride
    let v := if a.componentType == 5125 then (leU32 g.bin off).toNat else if a.componentType == 5123 then leU16 g.bin off else g.bin[off]!.toNat
    out := out.push v
  pure out

private def readUbyteVec4 (g : Glb) (ai : Nat) : Array Nat := Id.run do
  let a := g.accessors[ai]!
  let (base, stride) := accessorOffset g ai
  let mut out := Array.mkEmpty (a.count*4)
  for i in [:a.count] do
    let row := base + i*stride
    for k in [:4] do
      let v := if a.componentType == 5123 then leU16 g.bin (row + 2*k) else g.bin[row+k]!.toNat
      out := out.push v
  pure out

private def localMat (n : Node) : Mat4 := mat4FromTRS n.translation[0]! n.translation[1]! n.translation[2]! n.rotation[0]! n.rotation[1]! n.rotation[2]! n.rotation[3]! n.scale[0]! n.scale[1]! n.scale[2]!

private def localMatWith (n : Node) (t r sc : Option (Array Float)) : Mat4 :=
  let tr := t.getD n.translation
  let ro := r.getD n.rotation
  let sx := sc.getD n.scale
  mat4FromTRS tr[0]! tr[1]! tr[2]! ro[0]! ro[1]! ro[2]! ro[3]! sx[0]! sx[1]! sx[2]!

private def parentMap (nodes : Array Node) : Array (Option Nat) := Id.run do
  let mut p : Array (Option Nat) := Array.replicate nodes.size none
  for i in [:nodes.size] do for c in nodes[i]!.children do if c < nodes.size then p := p.set! c (some i)
  pure p

private def nodeWorlds (nodes : Array Node) (overrides : Std.HashMap Nat Mat4 := {}) : Array Mat4 := Id.run do
  let parents := parentMap nodes
  let n := nodes.size
  let mut worlds := Array.replicate n mat4Identity
  let mut done := Array.replicate n false
  let locals := nodes.mapIdx (fun i nd => (overrides[i]?).getD (localMat nd))
  for _ in [:n+2] do
    let mut any := false
    for i in [:n] do
      if !done[i]! then
        match parents[i]! with
        | none => worlds := worlds.set! i locals[i]!; done := done.set! i true; any := true
        | some p => if p < n && done[p]! then worlds := worlds.set! i (mat4Mul worlds[p]! locals[i]!); done := done.set! i true; any := true
    if !any then break
  worlds

private def readMat4Accessor (g : Glb) (ai : Nat) : Array Mat4 := Id.run do
  let fs := readFloatAccessor g ai
  let a := g.accessors[ai]!
  let mut out := Array.mkEmpty a.count
  for i in [:a.count] do out := out.push (fs.extract (i*16) (i*16+16))
  out


private def nearestIndex (times : Array Float) (time : Float) : Nat := Id.run do
  let mut best := 0
  let mut bestD := 1.0e30
  for i in [:times.size] do
    let d := (times[i]! - time).abs
    if d < bestD then best := i; bestD := d
  best

private def sampleTimes (g : Glb) : Array Float := Id.run do
  match g.animations[0]? with
  | none => #[0.0]
  | some a =>
    match a.samplers[0]? with
    | none => #[0.0]
    | some smp =>
      let ts := readFloatAccessor g smp.input
      if ts.isEmpty then #[0.0] else
      let n := ts.size
      let idxs := #[0, n/8, n/4, (3*n)/8, n/2, (5*n)/8, (3*n)/4, (7*n)/8, n-1]
      let mut out : Array Float := #[]
      for i in idxs do
        let j := if i < n then i else n-1
        let tm := ts[j]!
        if !out.any (fun x => (x - tm).abs < 0.00001) then out := out.push tm
      out

private def nodeWorldsAt (g : Glb) (time : Float) : Array Mat4 := Id.run do
  match g.animations[0]? with
  | none => nodeWorlds g.nodes
  | some anim =>
    let mut trans : Std.HashMap Nat (Array Float) := {}
    let mut rot : Std.HashMap Nat (Array Float) := {}
    let mut scl : Std.HashMap Nat (Array Float) := {}
    for ch in anim.channels do
      if ch.sampler < anim.samplers.size then
        let smp := anim.samplers[ch.sampler]!
        let ts := readFloatAccessor g smp.input
        let vals := readFloatAccessor g smp.output
        let outAcc := g.accessors[smp.output]!
        let width := comps outAcc.typeName
        if ts.size > 0 && width > 0 then
          let ki := nearestIndex ts time
          let value := vals.extract (ki*width) (ki*width+width)
          if ch.path == "translation" && value.size == 3 then trans := trans.insert ch.targetNode value
          else if ch.path == "rotation" && value.size == 4 then rot := rot.insert ch.targetNode value
          else if ch.path == "scale" && value.size == 3 then scl := scl.insert ch.targetNode value
    let mut overrides : Std.HashMap Nat Mat4 := {}
    for i in [:g.nodes.size] do
      if trans.contains i || rot.contains i || scl.contains i then
        overrides := overrides.insert i (localMatWith g.nodes[i]! trans[i]? rot[i]? scl[i]?)
    nodeWorlds g.nodes overrides

private def skinVerts (positions weights : Array Float) (joints : Array Nat) (skinJointNodes : Array Nat) (ibms : Array Mat4) (worlds : Array Mat4) : Array (Float × Float × Float) := Id.run do
  let n := positions.size / 3
  let mut out := Array.mkEmpty n
  for v in [:n] do
    let p := (positions[3*v]!, positions[3*v+1]!, positions[3*v+2]!)
    let mut acc := (0,0,0)
    for k in [:4] do
      let w := weights[4*v+k]!
      let ji := joints[4*v+k]!
      if w > 0 && ji < skinJointNodes.size then
        let node := skinJointNodes[ji]!
        let world := if node < worlds.size then worlds[node]! else mat4Identity
        let ibm := if ji < ibms.size then ibms[ji]! else mat4Identity
        acc := add3 acc (scale3 w (transformPoint (mat4Mul world ibm) p))
    out := out.push acc
  out

private def faceNormal (verts : Array (Float × Float × Float)) (a b c : Nat) :=
  if a < verts.size && b < verts.size && c < verts.size then normalize3 (cross3 (sub3 verts[b]! verts[a]!) (sub3 verts[c]! verts[a]!)) else (0,0,1)

private def dominantJoint (weights : Array Float) (joints : Array Nat) (v : Nat) : Nat := Id.run do
  let mut bj := 0; let mut bw := -1.0
  for k in [:4] do let w := weights[4*v+k]!; if w > bw then bw := w; bj := joints[4*v+k]!
  bj

private def edgeKey (a b : Nat) := if a <= b then s!"{a}:{b}" else s!"{b}:{a}"
private def nodeName (g : Glb) (i : Nat) :=
  match g.nodes[i]? with
  | some n => if n.name == "" then s!"node_{i}" else n.name
  | none => s!"node_{i}"

private def jointPairName (a b : String) : String :=
  if a <= b then s!"{a} <-> {b}" else s!"{b} <-> {a}"

private def isUpperArmTwist (s : String) : Bool :=
  s.startsWith "LeftArmTwistHelper" || s.startsWith "RightArmTwistHelper"

private def isTorsoShoulderArm (s : String) : Bool :=
  s.startsWith "Spine" || s.startsWith "LeftShoulder" || s.startsWith "RightShoulder" ||
  s.startsWith "LeftArm" || s.startsWith "RightArm"

private def isTargetFitPair (a b : String) : Bool :=
  (isUpperArmTwist a && isTorsoShoulderArm b) || (isUpperArmTwist b && isTorsoShoulderArm a)

private def reportPrimitive (g : Glb) (times : Array Float) (nodeIdx meshIdx primIdx skinIdx : Nat) (p : Primitive) : IO Nat := do
  let some ja := p.joints | return 0
  let some wa := p.weights | return 0
  let positions := readFloatAccessor g p.position
  let weights := readFloatAccessor g wa
  let joints := readUbyteVec4 g ja
  let indices := match p.indices with | some ia => readIndexAccessor g ia | none => Array.range (positions.size/3)
  let skin := g.skins[skinIdx]!
  let ibms := match skin.inverseBindMatrices with | some ai => readMat4Accessor g ai | none => Array.replicate skin.joints.size mat4Identity
  let baseVerts := skinVerts positions weights joints skin.joints ibms (nodeWorldsAt g times[0]!)
  let triN := indices.size / 3
  let mut baseNormals := Array.mkEmpty triN
  for t in [:triN] do baseNormals := baseNormals.push (faceNormal baseVerts indices[3*t]! indices[3*t+1]! indices[3*t+2]!)
  let mut first : Std.HashMap String Nat := {}
  let mut baseAngles : Std.HashMap String Float := {}
  for t in [:triN] do
    let a := indices[3*t]!; let b := indices[3*t+1]!; let c := indices[3*t+2]!
    for e in (#[(a,b),(b,c),(c,a)] : Array (Nat×Nat)) do
      let k := edgeKey e.1 e.2
      match first[k]? with
      | none => first := first.insert k t
      | some t0 => baseAngles := baseAngles.insert k (angleDeg baseNormals[t0]! baseNormals[t]!)
  let mut hits : Array (Float × String × String) := #[]
  let mut groups : Std.HashMap String (Nat × Float × String) := {}
  for fi in [:times.size] do
    let tm := times[fi]!
    let verts := skinVerts positions weights joints skin.joints ibms (nodeWorldsAt g tm)
    let mut norms := Array.mkEmpty triN
    for t in [:triN] do norms := norms.push (faceNormal verts indices[3*t]! indices[3*t+1]! indices[3*t+2]!)
    let mut seen : Std.HashMap String Nat := {}
    let mut edgeIdx := 0
    for t in [:triN] do
      let a := indices[3*t]!; let b := indices[3*t+1]!; let c := indices[3*t+2]!
      for e in (#[(a,b),(b,c),(c,a)] : Array (Nat×Nat)) do
        let k := edgeKey e.1 e.2
        match seen[k]? with
        | none => seen := seen.insert k t
        | some t0 =>
          let adeg := angleDeg norms[t0]! norms[t]!
          let bdeg := (baseAngles[k]?).getD 0.0
          let delta := adeg - bdeg
          if adeg >= 55.0 && delta >= 25.0 then
            let j0 := dominantJoint weights joints e.1; let j1 := dominantJoint weights joints e.2
            let n0 := if j0 < skin.joints.size then nodeName g skin.joints[j0]! else s!"joint_{j0}"
            let n1 := if j1 < skin.joints.size then nodeName g skin.joints[j1]! else s!"joint_{j1}"
            -- Problem-specific clothing-fit signal: upper-arm twist-helper
            -- discontinuities against torso/shoulder/upper-arm joints. This
            -- intentionally ignores same-joint folds plus unrelated hands,
            -- hips, feet, and finger creases so the report stays focused on
            -- the arm/torso garment kink under investigation.
            if n0 != n1 && isTargetFitPair n0 n1 then
              let pair := jointPairName n0 n1
              let line := s!"pair={pair} frame={fi} time={tm} delta={delta}° angle={adeg}° base={bdeg}° node={nodeName g nodeIdx} mesh={meshIdx} prim={primIdx} edge={edgeIdx} v=({e.1},{e.2})"
              hits := hits.push (delta, pair, line)
              match groups[pair]? with
              | none => groups := groups.insert pair (1, delta, line)
              | some old =>
                let count := old.1 + 1
                let bestDelta := old.2.1
                let bestLine := old.2.2
                if delta > bestDelta then groups := groups.insert pair (count, delta, line)
                else groups := groups.insert pair (count, bestDelta, bestLine)
        edgeIdx := edgeIdx + 1
  let sortedGroups := groups.toArray.qsort (fun a b =>
    let av := a.2; let bv := b.2
    if av.2.1 == bv.2.1 then av.1 > bv.1 else av.2.1 > bv.2.1)
  let sortedHits := hits.qsort (fun a b => a.1 > b.1)
  IO.println s!"node={nodeName g nodeIdx} mesh={meshIdx} prim={primIdx} upper_arm_clothing_fit_creases={sortedHits.size} joint_pairs={sortedGroups.size}"
  IO.println "  joint_pair_summary: count max_delta_deg representative_witness"
  for g0 in sortedGroups.extract 0 (min 8 sortedGroups.size) do
    IO.println s!"  pair={g0.1} count={g0.2.1} max_delta={g0.2.2.1}° witness={g0.2.2.2}"
  IO.println "  top_edge_witnesses:"
  for h in sortedHits.extract 0 (min 12 sortedHits.size) do IO.println s!"  {h.2.2}"
  return sortedHits.size

def run (path : System.FilePath) : IO Unit := do
  let g ← parseGlb path
  IO.println s!"glb={path} nodes={g.nodes.size} meshes={g.meshes.size} skins={g.skins.size} animations={g.animations.size}"
  let times := sampleTimes g
  IO.println s!"sample_frames={times.size}"
  let mut total := 0
  for ni in [:g.nodes.size] do
    match g.nodes[ni]!.mesh, g.nodes[ni]!.skin with
    | some mi, some si =>
      if mi < g.meshes.size && si < g.skins.size then
        let mesh := g.meshes[mi]!
        for pi in [:mesh.primitives.size] do total := total + (← reportPrimitive g times ni mi pi si mesh.primitives[pi]!)
    | _, _ => pure ()
  IO.println s!"total_upper_arm_clothing_fit_creases={total}"

end GltfCreaseDector

def main (args : List String) : IO Unit := do
  match args with
  | glb :: _ => GltfCreaseDector.run glb
  | _ => IO.eprintln "usage: gltf-crease-detector <model.glb>"; IO.Process.exit 2
