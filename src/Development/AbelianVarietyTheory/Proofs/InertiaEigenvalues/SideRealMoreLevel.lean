module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevelStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSmallerParahoricLevelModFirstBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperators

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PresHecke

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Raw

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} {inR : I → Prop} {isT isLoc : I → G → Prop}

theorem keepsDcRaw (P : ClassPres ι S σ ρ J χ) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (i : I) (hi : inR i) : Keeps P (dcL (W := W) (hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (hok i hi).2.2 Lc (fun a ha => hL1 _ ((hok i hi).2.1 a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _


open Classical in
def opRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keepsDcRaw P hx hA hok hloc i hi) else if one i then 1 else 0

def heckeRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) : HeckeTie ι P (opRaw P hχ hρ hx hA hok hloc one) inR isT isLoc where
  hx := hx
  hA := hA
  hx_ok i hi := (hok i hi).1
  hA_loc i hi := (hok i hi).2.1
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC i hi := (hok i hi).2.2
  op_eq i hi f := by
    unfold opRaw
    rw [dite_eq_left hi, ext_trE]
    rfl

end Raw

end GlobalTheory.PresHecke

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange GlobalTheory.PresHecke

theorem sideReal_ofPres : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  intro G Γ _ _ ι I c l isT isLoc K _ _ _ σ S G0 _ inR P hσ hρ red hsurj hker hx hA hok hloc one
  have hχ : ∀ k : l.J, ∃ b : K, σ b = (l.χ k : ℂ) := fun k => by rw [← l.ch_J]; exact hσ _
  exact ⟨actNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ,
    opRaw P hχ hρ hx hA hok hloc one,
    ⟨P, actTieNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ, heckeRaw P hχ hρ hx hA hok hloc one⟩,
    rfl, rfl, fun i hi => ⟨fun ho => by simp [opRaw, hi, ho], fun ho => by simp [opRaw, hi, ho]⟩⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperatorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  first | exact @GlobalTheory.sideReal_ofPres | exact GlobalTheory.sideReal_ofPres | (intros; apply GlobalTheory.sideReal_ofPres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatLevel

theorem hLat_mul_lev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  intro D V β Λ hΛ L y k hk
  have h : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ lev D.sp.cm V.gram β (Lev.flag1L L) := hk
  have hq : Formalism.UG.bc (Lev.swapAE D) k.1 ∈ St β := parLev_St h.1
  have hf : (1 : Bridge.Gf V).1 = Formalism.UG.bc (inclR (F := D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (1 : GL (Fin V.rank) D.host.E) := by
    rw [map_one]; exact OneMemClass.coe_one _
  have e := GlobalTheory.HLatMove.hLat_mul hΛ 1 y k 1 hf hq
  rw [one_mul] at e
  rw [e]
  ext x
  simp
end GlobalTheory.HLatLevel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeInvariantUnderLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitian_lattice_invariant_under_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (y k : Bridge.Gf V), k ∈ (levEnv V β L).J → Bridge.hLat V (y * k) = Bridge.hLat V y := by
  first | exact @GlobalTheory.HLatLevel.hLat_mul_lev | exact GlobalTheory.HLatLevel.hLat_mul_lev | (intros; apply GlobalTheory.HLatLevel.hLat_mul_lev <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatMatExists

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCharChange
open Formalism.IndefR.Lev

theorem ratMat_exists {D : D7} (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  have h := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨γE, -, e⟩ := Subgroup.mem_map.1 h
  exact ⟨γE, e.symm⟩

theorem flag_vals {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (hcg : ∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ))
    (hxq : ∀ PP ∈ L.Q, ∀ x, ∃ a, D.what₂.embLL a = ((L.xq PP x : ℂˣ) : ℂ)) (x) :
    ∃ a, D.what₂.embLL a = ((levFn β (flagL L) x : ℂˣ) : ℂ) := by
  have h1 : (flagL L).P.chi = 1 := rfl
  unfold levFn
  rw [h1, subgroupCharExtension_one_apply, one_mul]
  refine RingHom.mem_fieldRange.1 ?_
  simp only [Units.val_mul, Units.coe_prod]
  refine Subfield.mul_mem _ (Subfield.prod_mem _ fun PP hP => Subfield.prod_mem _ fun j hj => ?_)
    (Subfield.prod_mem _ fun PP hP => ?_)
  · obtain ⟨a, ha⟩ := hcg j (Finset.mem_range.1 hj) PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩
  · obtain ⟨a, ha⟩ := hxq PP hP _
    exact RingHom.mem_fieldRange.2 ⟨a, ha⟩

end GlobalTheory.TwistCharChange
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideRealMoreLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SideLevel
open Formalism.IndefR.Lev

theorem surj_restrict {A G : Type} [Group A] [Group G] {J Q Q' : Subgroup A} (h : Q' ≤ Q) (red : Q →* G)
    (hs : Function.Surjective red) (hk : ∀ q : Q, red q = 1 ↔ (q : A) ∈ J)
    (hm : ∀ g ∈ Q, ∃ g' ∈ Q', g⁻¹ * g' ∈ J) : Function.Surjective (red.comp (Subgroup.inclusion h)) := by
  intro g
  obtain ⟨q, rfl⟩ := hs g
  obtain ⟨g', hg', hJ⟩ := hm q q.2
  refine ⟨⟨g', hg'⟩, ?_⟩
  have h1 : red (q⁻¹ * ⟨g', h hg'⟩) = 1 := (hk _).2 hJ
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm



theorem sideReal_moreLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok ok' : Set Pl0) (Sp : Set (Pl D.host.E)), L.Q ⊆ Q' → ok' ⊆ ok → (∀ PP ∈ L.Pg, ∀ PP' ∈ Q', PP ≠ PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP PP' ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP' PP) → (∀ P ∈ ok', Bridge.SplitOff (pl P) Sp) → (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ∈ Sp) → (∀ j, j < L.s → ∀ PP ∈ L.Pg, ∀ x, ∃ a, D.what₂.embLL a = ((L.cg (j + 1) PP x : ℂˣ) : ℂ)) → (∀ PP ∈ Q', ∀ x, ∃ a, D.what₂.embLL a = ((xq PP x : ℂˣ) : ℂ)) → ∀ (c : Bridge.CoefDat D V) (S : CSD D.what₂.LL) (act : Representation D.what₂.LL G S.Forms) (op : ok × ℕ → Module.End D.what₂.LL S.Forms) (B : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β L pl ok)) S act op (fun i => i.2)), (∃ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (rho : _) (pair : _) (nab del : _), Bridge.CoefMapTie V c c0 rho ∧ Bridge.CoefTie V c B.pres lam c0 pair nab del) → ∃ (S' : CSD D.what₂.LL) (act' : Representation D.what₂.LL G S'.Forms) (op' : ok' × ℕ → Module.End D.what₂.LL S'.Forms) (B' : Bridge.SideReal D V (Bridge.envOf c (levEnvOf V β { L with Q := Q', xq := xq } pl ok')) S' act' op' (fun i => i.2)), (∀ q : (levEnv V β { L with Q := Q', xq := xq }).Q, ∃ hq : (q : Bridge.Gf V) ∈ (levEnv V β L).Q, B'.act_tie.red q = B.act_tie.red ⟨q, hq⟩) ∧ (∀ (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) pair nab del, Bridge.CoefTie V c B.pres lam c0 pair nab del → Bridge.CoefTie V c B'.pres lam c0 pair nab del) ∧ ∀ P, op' (P, 0) = 1 ∧ ∀ k, V.rank < k → op' (P, k) = 0 := by
  intro D G _ _ V β Λ hSD L Q' xq Pl0 pl ok ok' Sp hQ hok hdisj hsplit hS hcg hxq c S act op B hct
  have hfin := GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ
  obtain ⟨hJle, hQle, hfi, hker⟩ := hfin
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  have hSD' : IsSDFrame V β Λ 1 := ⟨cc, by rw [one_pow]; exact hβ⟩
  let L' : LevDat D.host.E ℂ V.rank := { L with Q := Q', xq := xq }
  have hval : ∀ q : (levEnv V β L').Q, ∃ a, D.what₂.embLL a = (((levEnv V β L').ch q : ℂˣ) : ℂ) :=
    fun q => GlobalTheory.TwistCharChange.flag_vals V β L' hcg hxq _
  have hvalJ : ∀ k : (levEnv V β L').J, ∃ a, D.what₂.embLL a = (((levEnv V β L').χ k : ℂˣ) : ℂ) := by
    intro k
    rw [← (levEnv V β L').ch_J k]
    exact hval _
  have hrat : ∀ (γ : GQ V) x, ∃ x', B.pres.coef x' = c.ρ γ (B.pres.coef x) := by
    obtain ⟨lam, c0, rho, pair, nab, del, hmap, e, -, hco, -⟩ := hct
    intro γ x
    obtain ⟨γE, hγ⟩ := GlobalTheory.TwistCharChange.ratMat_exists V γ
    refine ⟨e.symm (rho γE (e x)), ?_⟩
    refine ((hco _).trans ?_).trans (congrArg (c.ρ γ) (hco x)).symm
    rw [LinearEquiv.apply_symm_apply]
    exact hmap.1 γ γE hγ (e x)
  obtain ⟨Cl, fC, π, kc, Gam, gG, fG, ρ', P', hy, hcoef⟩ := GlobalTheory.T.classPres_of_finiteIndex_subLevel (Bridge.ratF V) D.what₂.embLL S c.ρ
    (levEnv V β L).J (levEnv V β L).χ B.pres (levEnv V β L').J hJle hfi (levEnv V β L').χ hvalJ hrat
  have hrat' : ∀ (γ : GQ V) x, ∃ x', P'.coef x' = c.ρ γ (P'.coef x) := by
    rw [hcoef]; exact hrat

  let red' : (levEnv V β L').Q →* G := B.act_tie.red.comp (Subgroup.inclusion hQle)
  have hred_surj : Function.Surjective red' :=
    surj_restrict hQle B.act_tie.red B.act_tie.red_surj B.act_tie.red_ker (GlobalTheory.T.exists_mem_smaller_parahoricLevel_mod_firstBlocks D V β Λ hSD' L Q' xq hQ hdisj)
  have hred_ker : ∀ q : (levEnv V β L').Q, red' q = 1 ↔ (q : Bridge.Gf V) ∈ (levEnv V β L').J := by
    intro q
    exact (B.act_tie.red_ker ⟨q, hQle q.2⟩).trans ⟨fun h => hker _ q.2 h, fun h => hJle h⟩

  let up : ok' × ℕ → ok × ℕ := fun i => (⟨i.1, hok i.1.2⟩, i.2)
  have hoffI : ∀ i : ok' × ℕ, ∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1) :=
    fun i PP h => GlobalTheory.SplitHeckeAdj.off_of_splitOff (hsplit i.1.1 i.1.2) PP (hS PP h)
  have hHk : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → isTEnv V pl ok' i (B.hecke.hx (up i)) ∧
      (∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok' i a) ∧ Bridge.IsDC (levEnv V β L').J (B.hecke.hx (up i)) (B.hecke.hA (up i)) := by
    intro i hi
    have hT : isTEnv V pl ok (up i) (B.hecke.hx (up i)) := B.hecke.hx_ok (up i) hi
    have hA : ∀ a ∈ B.hecke.hA (up i), isLocEnv V pl ok (up i) a := B.hecke.hA_loc (up i) hi
    refine ⟨hT, hA, ?_⟩
    exact GlobalTheory.T.hecke_representatives_split_place_smaller_level D V β Λ hSD' L Q' xq hQ Pl0 pl ok (up i) (hoffI i) hi.2 _ _ hT hA (B.hecke.hDC (up i) hi)
  have hloc : ∀ i : ok' × ℕ, (1 ≤ i.2 ∧ i.2 ≤ V.rank) → ∃ Lc : Subgroup (Bridge.Gf V),
      (∀ x, isLocEnv V pl ok' i x → x ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L').J, ∃ k₁ ∈ (levEnv V β L').J, ∃ k₂ ∈ (levEnv V β L').J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧
        ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : (levEnv V β L').J, (k : Bridge.Gf V) ∈ Lc → (levEnv V β L').χ k = 1 := by
    intro i hi
    obtain ⟨α, hα, -⟩ := B.hecke.hx_ok (up i) hi hi.2
    obtain ⟨e, -, he, -⟩ := hα
    obtain ⟨Lc, l1, l2, l3, -⟩ := GlobalTheory.SplitHeckeAdj.local_group V β Λ L' hβ (pl i.1) e he (hoffI i)
    refine ⟨Lc, fun x hx => ?_, l2, l3⟩
    obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp V hx he
    exact l1 g hg
  obtain ⟨act', op', B', hpres, hred, hop⟩ := GlobalTheory.T.classPres_forms_finiteGroup_heckeOperators (Bridge.ratF V) c (levEnv V β L') (isTEnv V pl ok')
    (isLocEnv V pl ok') D.what₂.embLL _ (fun i : ok' × ℕ => 1 ≤ i.2 ∧ i.2 ≤ V.rank) P' hval hrat' red' hred_surj hred_ker
    (fun i => B.hecke.hx (up i)) (fun i => B.hecke.hA (up i)) hHk hloc (fun i => i.2 = 0)
  subst hpres
  have hl : ∀ cl, Bridge.hLat V (B'.pres.y cl) = Bridge.hLat V (B.pres.y (π cl)) := fun cl =>
    (congrArg (Bridge.hLat V) (hy cl)).trans (GlobalTheory.T.hermitian_lattice_invariant_under_level D V β Λ hSD' L _ _ (kc cl).2)
  refine ⟨_, act', op', B', fun q => ⟨hQle q.2, DFunLike.congr_fun hred q⟩, ?_, ?_⟩
  · rintro lam c0 pair nab del ⟨e, h1, h2, h3, h4, h5⟩
    exact ⟨e, h1, fun x => (DFunLike.congr_fun hcoef x).trans (h2 x), h3,
      fun cl => (h4 (π cl)).trans (congrArg nab (hl cl).symm), fun cl => (h5 (π cl)).trans (congrArg del (hl cl).symm)⟩
  · intro P
    refine ⟨(hop (P, 0) (by simp)).1 rfl, fun k hk => (hop (P, k) (by simp only [not_and, not_le]; intro; omega)).2 (by simp only; omega)⟩

end GlobalTheory.SideLevel
end
end
