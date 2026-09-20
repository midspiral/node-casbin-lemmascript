import Lake
open Lake DSL System

require velvet from ".." / "velvet"
require LemmaScript from ".." / "LemmaScript"

package CasbinLemmaScript where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib Effector where
  srcDir := "src/effect"
  roots := #[`«effectorPure.types», `«effectorPure.spec», `«effectorPure.def», `«effectorPure.proof»]

@[default_target]
lean_lib Util where
  srcDir := "src/util"
  roots := #[`«arrayEquals.def», `«arrayEquals.proof», `«keyMatch.types», `«keyMatch.def», `«keyMatch.proof», `«keyGet.types», `«keyGet.def», `«keyGet.proof»]

@[default_target]
lean_lib Model where
  srcDir := "src/model"
  roots := #[`«getFilteredPolicy.def», `«getFilteredPolicy.proof»]
