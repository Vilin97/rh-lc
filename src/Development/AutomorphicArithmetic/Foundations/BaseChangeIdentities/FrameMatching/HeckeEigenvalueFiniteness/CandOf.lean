module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.EigList
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemDCand
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemDCand

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.StrictCommon

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem strict_common {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P Q R : Pre E n} (h1 : Strict P R)
    (h2 : Strict Q R) : Strict P Q := by
  obtain ⟨a1, c1, m1⟩ := h1
  obtain ⟨a2, c2, m2⟩ := h2
  refine ⟨?_, c1.trans c2.symm, fun i => ?_⟩
  · refine Tw.FiniteStrictOrder.forall₂_ofFn SIso (c1.trans c2.symm) _ _ fun i => ?_
    have hi : i.val < R.c := c1 ▸ i.isLt
    have e1 := (List.forall₂_iff_get.1 a1).2 i.val (by simp [parts]) (by simpa [parts] using hi)
    have e2 := (List.forall₂_iff_get.1 a2).2 i.val (by simpa [parts, c2] using hi) (by simpa [parts] using hi)
    simp only [parts, List.get_ofFn] at e1 e2
    exact Tw.FiniteStrictOrder.siso_trans (Q.discrete _).stable e1 e2
  · rw [m1 i, m2]
    rfl

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.SameOfStrict

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem joins_fin (hSJ : StrictJoin)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (μ : HChar E) {ι : Type} [Finite ι] (a : ι → ℕ) (kA kB : ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - a i)) :
    ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i (Pa : Pre E (a i)) (Pb : Pre E (n - a i)) (D : Pre E n),
      IsJoin (μ ^ (n - a i)) (μ ^ a i) Pa Pb D → (∃ ja, Strict Pa (PA i ja)) → (∃ jb, Strict Pb (PB i jb)) →
      ∃ j, Strict D (Dl j) := by
  let J : Type := {x : Σ i, Fin (kA i) × Fin (kB i) // ∃ D : Pre E n, ∃ (Pa : Pre E (a x.1)) (Pb : Pre E (n - a x.1)),
    IsJoin (μ ^ (n - a x.1)) (μ ^ a x.1) Pa Pb D ∧ Strict Pa (PA x.1 x.2.1) ∧ Strict Pb (PB x.1 x.2.2)}
  haveI : Finite J := Subtype.finite
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  choose Df Paf Pbf hf using fun x : J => x.2
  refine ⟨k, fun j => Df (e.symm j), fun i Pa Pb D hj ⟨ja, ha⟩ ⟨jb, hb⟩ => ?_⟩
  let x : J := ⟨⟨i, ja, jb⟩, D, Pa, Pb, hj, ha, hb⟩
  refine ⟨e x, ?_⟩
  show Strict D (Df (e.symm (e x)))
  rw [e.symm_apply_apply]
  exact hSJ E n _ _ _ _ Pa (Paf x) Pb (Pbf x) D _ hj (hf x).1 (strict_common ha (hf x).2.1) (strict_common hb (hf x).2.2)

theorem same_of_strict (hSPr : StrictProd) (hII : IsoInv) (hAd : AdmProd)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w))
    (ho : IsOpen (K : Set (GLw n w))) (hle : K ≤ GlobalTheory.LFun.KGL w (n := n)) (D D' : Pre E n) (hs : Strict D D') :
    (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
      Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
      FiniteDimensional ℂ ↥(fixed (prodAt D' w) K) := by
  have h := hII (GLw n w) _ _ (prodAt D w) (prodAt D' w) (hSPr E n D D' hs w) K
  exact ⟨fun τ => h.1 τ.V τ.ρ, h.2.1, hAd E n D' w K ho hle⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ImportsAlt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

def Same {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) (K : Subgroup (GLw n w)) (D D' : Pre E n) : Prop :=
  (∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) ↔ GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D' w)) ∧
    Module.finrank ℂ ↥(fixed (prodAt D w) K) = Module.finrank ℂ ↥(fixed (prodAt D' w) K) ∧
    FiniteDimensional ℂ ↥(fixed (prodAt D' w) K)

theorem part2 (hSPr : StrictProd) (hSJ : StrictJoin) (hII : IsoInv) (hAd : AdmProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) :
    ∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j) := by
  intro w hw
  obtain ⟨k, Dl, hD⟩ := joins_fin hSJ F₀.μ F₀.C.a kA kB PA PB
  have hs : ∀ D D' : Pre E n, Strict D D' → Same w (F₀.d₀.K' w) D D' :=
    same_of_strict hSPr hII hAd w _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1
  refine ⟨k, Dl, fun i s₁ s₂ Pa Pb D hc => ?_⟩
  obtain ⟨j, hj⟩ := hD i Pa Pb D hc.ctx.join (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2
  exact ⟨j, hs D (Dl j) hj⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.ClsFin

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem rl_levels (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (h1 : IsOpen (K₁ : Set (GL (Fin a) (Af E)))) (h2 : IsOpen (K₂ : Set (GL (Fin b) (Af E)))) :
    Levels E (rlΘ₁ hR E a b Ma Mb K₁ K₂) ∧ Levels E (rlΘ₂ hR E a b Ma Mb K₁ K₂) :=
  (hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 a b Ma Mb K₁ K₂ h1 h2

theorem rl_ktypes (hR : Rd.ReadLimit) (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Ma : Mods E a)
    (Mb : Mods E b) : KTypes E (rlΩ₁ hR E a b Ma Mb) ∧ KTypes E (rlΩ₂ hR E a b Ma Mb) :=
  ⟨((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.1,
    ((hR E).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 a b Ma Mb).2.2.2.1⟩

theorem cls_fin (hFS : FinStrict) (hCP : CandParts)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (i : F₀.C.ι)
    (h1 : IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))))
    (h2 : IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
      F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
  have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ h1 h2
  have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
  obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
  obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
  refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
  have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
  have hm := LemDd.cand_sum hc
  exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.Imports

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem part1 (hII : IsoInv) (hSPr : StrictProd) {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (kA kB : F₀.C.ι → ℕ)
    (PA : ∀ i, Fin (kA i) → Pre E (F₀.C.a i)) (PB : ∀ i, Fin (kB i) → Pre E (n - F₀.C.a i))
    (hcls : ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA i ja)) ∧ ∃ jb, Strict Pb (PB i jb)) (T' : Finset (Pl E)) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  choose Z mZ hZ using fun (i : F₀.C.ι) (w : Pl E) => eig_fin hII hSPr (PA i) (PB i) w (F₀.d₀.ϖ w)
  refine ⟨fun i w => ⟨Z i w, (hZ i w).1, fun s₁ s₂ Pa Pb D hc _ => ?_⟩,
    ⟨Finset.univ.sup fun i => T'.sup (mZ i), fun i s₁ s₂ Pa Pb D hc w hw => ?_⟩⟩
  · exact ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).2
  · have h1 := ((hZ i w).2 Pa Pb (hcls i s₁ s₂ Pa Pb D hc).1 (hcls i s₁ s₂ Pa Pb D hc).2).1
    have h2 : mZ i w ≤ T'.sup (mZ i) := Finset.le_sup hw
    have h3 : T'.sup (mZ i) ≤ Finset.univ.sup fun i => T'.sup (mZ i) :=
      Finset.le_sup (f := fun i => T'.sup (mZ i)) (Finset.mem_univ i)
    exact le_trans h1 (le_trans h2 h3)

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.CandOf

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical




attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

theorem all_parts (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts) (hII : IsoInv) (hAd : AdmProd)
    {hR : Rd.ReadLimit} {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (d : LocData E n) (T' : Finset (Pl E))
    (hO : ∀ i : F₀.C.ι, IsOpen (lev₁ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (F₀.C.a i)) (Af E))) ∧
      IsOpen (lev₂ F₀.Sec d (F₀.C.a i) : Set (GL (Fin (n - F₀.C.a i)) (Af E)))) :
    (∀ i w, ∃ Z : Set ((Fin (F₀.C.a i) → ℂˣ) × (Fin (n - F₀.C.a i) → ℂˣ)), Z.Finite ∧
      ∀ s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → w ∈ T' → ∀ ξa ξb, JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb → (ξa, ξb) ∈ Z) ∧
    (∀ w ∈ F₀.d₀.S₀, ∃ (k : ℕ) (Dl : Fin k → Pre E n), ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D →
      ∃ j, Same w (F₀.d₀.K' w) D (Dl j)) ∧
    ∃ m₀ : ℕ, ∀ i s₁ s₂ Pa Pb D, F₀.Cand d i s₁ s₂ Pa Pb D → ∀ w ∈ T', dimI Pa Pb w ≤ m₀ := by
  have hfin (i : F₀.C.ι) :
      ∃ (kA kB : ℕ) (PA : Fin kA → Pre E (F₀.C.a i)) (PB : Fin kB → Pre E (n - F₀.C.a i)), ∀ s₁ s₂ Pa Pb D,
        F₀.Cand d i s₁ s₂ Pa Pb D → (∃ ja, Strict Pa (PA ja)) ∧ ∃ jb, Strict Pb (PB jb) := by
    have hL := rl_levels hR E _ _ (F₀.A i).Ma (F₀.A i).Mb _ _ (hO i).1 (hO i).2
    have hK := rl_ktypes hR E _ _ (F₀.A i).Ma (F₀.A i).Mb
    obtain ⟨kA, PA, hPA⟩ := hFS E _ _ _ hL.1 hK.1 (mOf (F₀.A i).χa)
    obtain ⟨kB, PB, hPB⟩ := hFS E _ _ _ hL.2 hK.2 (mOf (F₀.A i).χb)
    refine ⟨kA, kB, PA, PB, fun s₁ s₂ Pa Pb D hc => ?_⟩
    have hp := hCP hR E n π S F₀ d i s₁ s₂ Pa Pb D hc
    have hm := LemDd.cand_sum hc
    exact ⟨hPA Pa hp.1 hm.1, hPB Pb hp.2 hm.2⟩
  choose kA kB PA PB hcls using hfin
  have h1 := part1 hII hSPr F₀ d kA kB PA PB hcls T'
  exact ⟨h1.1, part2 hSPr hSJ hII hAd F₀ d kA kB PA PB hcls, h1.2⟩

theorem candFin_of (hFS : FinStrict) (hSPr : StrictProd) (hSJ : StrictJoin) (hCP : CandParts)
    (hLO : LevOpen) (hII : IsoInv) (hAd : AdmProd) : CandFin := by
  intro hR E _ _ _ hU n hn π hπ S F₀ T' c e b hT'
  have hO := fun i : F₀.C.ι => hLO hR E n π S F₀ T' c e b (F₀.C.a i) (F₀.C.le i)
  exact all_parts hFS hSPr hSJ hCP hII hAd F₀ (F₀.loc T' c e b) T' hO

end UpperTheory.HeckeLevelFrameExistence.CF

end
end
end
