import Lake

open System Lake DSL

package ElevenTwelfths where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require «rellich-kondrachov» from git
  "https://github.com/abenenson/rellich-kondrachov.git" @
    "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23"

-- Keep mathlib last: this pin overrides the older revision requested by the
-- Rellich--Kondrachov package, exactly as in OpenAI's source build.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

/- OpenAI's Lean 4.34.1 compatibility patch for Rellich--Kondrachov is
applied after dependency resolution.  This is the relevant part of the
upstream project's patch hook, kept here so a fresh clone is reproducible. -/
private def patchGit (directory : FilePath) (args : Array String) :
    IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args := #["-C", directory.toString] ++ args }

private def checkPatch (directory patch : FilePath) (args : Array String := #[]) :
    IO IO.Process.Output :=
  patchGit directory (#["apply", "--check"] ++ args ++ #[patch.toString])

private inductive PatchState where
  | absent
  | applied
  | needsApply

private structure PatchPlan where
  label : String
  directory : FilePath
  patch : FilePath
  url : String
  revision : String
  state : PatchState

private def planDependencyPatch (root : FilePath) (dependency : Dependency) :
    IO PatchPlan := do
  let label := dependency.dirName
  let some (.git url (some revision) none) := dependency.src?
    | throw <| IO.userError
        s!"{label}: compatibility patches require a Git dependency pinned to a commit."
  unless revision.length == 40 && revision.toList.all (fun c =>
      c.isDigit || ('a' <= c && c <= 'f')) do
    throw <| IO.userError
      s!"{label}: expected a full lowercase Git commit, got {revision}."
  let patch := root / "upstream" / "patches" /
    "rellich-kondrachov-lean4341.patch"
  unless ← patch.pathExists do
    throw <| IO.userError s!"Missing compatibility patch: {patch}"
  let directory := root / ".lake" / "packages" / label
  let plan := { label, directory, patch, url, revision, state := .absent : PatchPlan }
  unless ← directory.pathExists do
    return plan
  let head ← patchGit directory #["rev-parse", "HEAD"]
  unless head.exitCode == 0 && head.stdout.trimAscii.toString == revision do
    throw <| IO.userError
      s!"{label}: expected commit {revision}, got {head.stdout}\n{head.stderr}"
  let origin ← patchGit directory #["remote", "get-url", "origin"]
  unless origin.exitCode == 0 && origin.stdout.trimAscii.toString == url do
    throw <| IO.userError
      s!"{label}: expected origin {url}, got {origin.stdout}\n{origin.stderr}"
  let reverse ← checkPatch directory patch #["--reverse"]
  if reverse.exitCode == 0 then
    return { plan with state := .applied }
  let forward ← checkPatch directory patch
  if forward.exitCode == 0 then
    return { plan with state := .needsApply }
  throw <| IO.userError
    s!"{label}: compatibility patch conflicts with local changes.\n\
      Forward check:\n{forward.stderr}\nReverse check:\n{reverse.stderr}"

private def applyDependencyPatch (plan : PatchPlan) (directory : FilePath) : IO Unit := do
  let applied ← patchGit directory #["apply", plan.patch.toString]
  unless applied.exitCode == 0 do
    throw <| IO.userError
      s!"{plan.label}: failed to apply compatibility patch:\n{applied.stderr}"
  let verified ← checkPatch directory plan.patch #["--reverse"]
  unless verified.exitCode == 0 do
    throw <| IO.userError
      s!"{plan.label}: patch verification failed:\n{verified.stderr}"

private def preparePatchedDependency (root : FilePath) (dependency : Dependency) :
    IO Bool := do
  let plan ← planDependencyPatch root dependency
  match plan.state with
  | .applied => return false
  | .needsApply =>
    applyDependencyPatch plan plan.directory
    return true
  | .absent =>
    let packages := root / ".lake" / "packages"
    IO.FS.createDirAll packages
    let pid ← IO.Process.getPID
    let stamp ← IO.monoNanosNow
    let staging := packages / s!".{plan.label}-bootstrap-{pid}-{stamp}"
    IO.FS.createDir staging
    try
      let cloned ← IO.Process.output {
        cmd := "git", args := #["clone", "--no-checkout", plan.url, staging.toString]
      }
      unless cloned.exitCode == 0 do
        throw <| IO.userError s!"{plan.label}: clone failed:\n{cloned.stderr}"
      let checkedOut ← patchGit staging #["checkout", "--detach", plan.revision]
      unless checkedOut.exitCode == 0 do
        throw <| IO.userError
          s!"{plan.label}: checkout failed:\n{checkedOut.stderr}"
      applyDependencyPatch plan staging
      IO.FS.rename staging plan.directory
      return true
    finally
      if ← staging.pathExists then
        IO.FS.removeDirAll staging

-- Configuration elaboration precedes dependency resolution.  Applying the
-- patch here makes `lake exe cache get` the first required command in a fresh
-- clone, as in the OpenAI source project.
run_cmd do
  let env ← Lean.getEnv
  if let some root := Lake.dirExt.getState env then
    let options ← Lean.getOptions
    let changed ← Lean.Elab.Command.liftIO do
      let declarations ← IO.ofExcept <| Lake.packageDepAttr.getAllEntries env |>.mapM
        fun name => unsafe env.evalConstCheck Dependency options ``Dependency name
      let some dependency := declarations.find? (·.name == `«rellich-kondrachov»)
        | throw <| IO.userError "Missing direct dependency rellich-kondrachov."
      preparePatchedDependency root dependency
    if changed then
      Lean.logInfo "rellich-kondrachov: applied compatibility patch before dependency resolution"

post_update pkg do
  let name := `«rellich-kondrachov»
  let label := name.toString (escape := false)
  let some dependency ← findPackageByName? name
    | error s!"Missing dependency {label}; run lake update from the project root."
  let some declaration := pkg.depConfigs.find? (·.name == name)
    | error s!"Missing direct dependency declaration for {label}."
  let some (.git _ (some revision) _) := declaration.src?
    | error s!"{label} must be pinned to a Git commit."
  let head ← patchGit dependency.dir #["rev-parse", "HEAD"]
  unless head.exitCode == 0 && head.stdout.trimAscii.toString == revision do
    error s!"{label}: expected commit {revision}, got {head.stdout}\n{head.stderr}"
  let patch := pkg.dir / "upstream" / "patches" /
    "rellich-kondrachov-lean4341.patch"
  unless ← patch.pathExists do
    error s!"Missing compatibility patch: {patch}"
  let reverse ← checkPatch dependency.dir patch #["--reverse"]
  if reverse.exitCode == 0 then
    logInfo s!"{label}: compatibility patch already applied"
  else
    let forward ← checkPatch dependency.dir patch
    unless forward.exitCode == 0 do
      error s!"{label}: compatibility patch conflicts with local changes.\n\
        Forward check:\n{forward.stderr}\nReverse check:\n{reverse.stderr}"
    let result ← patchGit dependency.dir #["apply", patch.toString]
    unless result.exitCode == 0 do
      error s!"{label}: failed to apply compatibility patch:\n{result.stderr}"
    let verified ← checkPatch dependency.dir patch #["--reverse"]
    unless verified.exitCode == 0 do
      error s!"{label}: patch verification failed:\n{verified.stderr}"
    logInfo s!"{label}: applied Lean 4.34.1 compatibility patch"

lean_lib OAI where
  globs := #[`OAI.+]

@[default_target] lean_lib ElevenTwelfths where
  globs := #[`ElevenTwelfths, `ElevenTwelfths.+]
