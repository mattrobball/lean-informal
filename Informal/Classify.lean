/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean

/-!
# Declaration classification and resolution

Provides a fine-grained classification of non-user-facing declarations
and a recursive resolution function that maps any declaration to its
user-facing parent.
-/

public meta section

open Lean Meta

namespace Informal

/-- Why a declaration is not user-facing, carrying enough info to resolve to the parent. -/
inductive NonUserReason where
  | isInternal
  | isImplDetail
  | isProjection   (structName : Name)
  | isAuxRec
  | isNoConf
  | isMatcher
  | isCtorIdx      (inductName : Name)
  | isCtor         (inductName : Name)
  | isRec          (inductName : Name)
  | isQuot
  | isEqnLemma     (defName : Name)
  | isReserved
  | isCtorDeriv    (inductName : Name)
  | isNoConfTy
  | hasNoRange

/-- Given a `NonUserReason`, return the parent name that this declaration derives from. -/
def NonUserReason.parent (name : Name) : NonUserReason → Name
  | .isProjection structName    => structName
  | .isCtor inductName          => inductName
  | .isRec inductName           => inductName
  | .isCtorIdx inductName       => inductName
  | .isCtorDeriv inductName     => inductName
  | .isEqnLemma defName        => defName
  | _                           => name.getPrefix

/-- Classify a declaration as non-user-facing, returning `some reason` if it is
a compiler-generated or auxiliary declaration, or `none` if it is user-facing. -/
private def checkCtorIdx? (env : Environment) (name : Name) : Option NonUserReason :=
  if let .str indName "ctorIdx" := name then
    match isInductiveCore? env indName with
    | some iv => some (.isCtorIdx iv.name)
    | none    => none
  else none

private def checkNoRange (ci? : Option ConstantInfo) (env : Environment) (name : Name) :
    Option NonUserReason :=
  if ci?.isSome &&
      (declRangeExt.find? (level := .exported) env name).isNone &&
      (declRangeExt.find? (level := .server) env name).isNone then
    some .hasNoRange
  else none

def classifyNonUser (env : Environment) (name : Name) : Option NonUserReason :=
  if name.isInternal then some .isInternal
  else if name.isImplementationDetail then some .isImplDetail
  else if let some info := env.getProjectionFnInfo? name then
    some <| .isProjection <| match env.find? info.ctorName with
      | some (.ctorInfo cv) => cv.induct
      | _                   => name.getPrefix
  else if isAuxRecursor env name then some .isAuxRec
  else if isNoConfusion env name then some .isNoConf
  else if isMatcherCore env name then some .isMatcher
  else if let some r := checkCtorIdx? env name then some r
  else match env.find? name with
    | some (.ctorInfo cv) => some (.isCtor cv.induct)
    | some (.recInfo rv)  => some (.isRec (rv.all.head?.getD name.getPrefix))
    | some (.quotInfo _)  => some .isQuot
    | ci? =>
      if let some (defName, _) := declFromEqLikeName env name then some (.isEqnLemma defName)
      else if isReservedName env name then some .isReserved
      else match name with
        | .str p s =>
          if s == "inj" || s == "injEq" || s == "sizeOf_spec" then
            match env.find? p with
            | some (.ctorInfo cv) => some (.isCtorDeriv cv.induct)
            | _                   => checkNoRange ci? env name
          else if s == "noConfusionType" then some .isNoConfTy
          else checkNoRange ci? env name
        | _ => checkNoRange ci? env name

/-- Recursively resolve a name to its user-facing parent declaration.
Strips `_private` wrappers, then follows `classifyNonUser` until the name
is user-facing or fuel runs out. -/
def resolveToUser (env : Environment) (name : Name) (fuel : Nat := 8) : Name :=
  let name := (privateToUserName? name).getD name
  match fuel, classifyNonUser env name with
  | 0, _           => name
  | _, none         => name
  | n+1, some reason => resolveToUser env (reason.parent name) n

end Informal

end
