module

public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreGen
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreHarm
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreRoot
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSplit
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSupp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.ExistsMonomialWeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.ConjTransposeOneKronecker
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreStar

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem star_inj_quot {M T : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    (D : Module.End ℂ M) (D' : Module.End ℂ T) (π : M →ₗ[ℂ] T) (hπ : ∀ x, D' (π x) = π (D x))
    (Y : Submodule ℂ M) [FiniteDimensional ℂ Y] (hY : ∀ y ∈ Y, D y ∈ Y) (hi : ∀ y ∈ Y, D y = 0 → y = 0)
    {y : M} (hy : y ∈ Y) (h0 : D' (π y) = 0) : π y = 0 := by
  let Z : Submodule ℂ M := Y ⊓ LinearMap.ker π
  haveI : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
  have hZ : ∀ z ∈ Z, D z ∈ Z := by
    intro z hz
    refine ⟨hY z hz.1, ?_⟩
    have h2 : π z = 0 := hz.2
    show π (D z) = 0
    rw [← hπ, h2, map_zero]
  have hinj : Function.Injective (D.restrict hZ) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    have h3 : D z.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hz)
    exact Subtype.ext (hi z.1 z.2.1 h3)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hDy : D y ∈ Z := ⟨hY y hy, by
    show π (D y) = 0
    rw [← hπ, h0]⟩
  obtain ⟨z, hz⟩ := hsurj ⟨D y, hDy⟩
  have hz' : D z.1 = D y := congrArg Subtype.val hz
  have h4 : y - z.1 = 0 := hi _ (Y.sub_mem hy z.2.1) (by rw [map_sub, hz', sub_self])
  have h5 : y = z.1 := sub_eq_zero.1 h4
  rw [h5]
  exact z.2.2

theorem star_casK_mem {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Ix r s → Ix r s → Module.End ℂ M} {Y : Submodule ℂ M} (hY : KSt ρ Y) {y : M} (hy : y ∈ Y) :
    casK ρ y ∈ Y := by
  unfold casK
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hY a b h _ (hY b a (PI.FHS.sameBlock_symm h) _ hy)
  · simp

theorem star_trace {r s : ℕ} (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; simp
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

theorem star_tw {p q r s : ℕ} (τ : ℂ) (a b : Ix r s) (g : Pol p q r s) :
    units (twAct p q r s τ) a b g =
      units (fockAct2 p q r s) a b g + (if a = b then τ else 0) • g := by
  unfold units
  rw [twAct_apply, star_trace]
  split_ifs <;> simp

theorem star_cas_mk {p q r s : ℕ} (c τ : ℂ) (g : Pol p q r s) :
    casK (units (thAct p q r s c τ)) (thMkC p q r s c g) =
      thMkC p q r s c (casK (units (twAct p q r s τ)) g) := by
  unfold casK

  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · simp only [Module.End.mul_apply, units, thAct_mk]
  · simp

theorem star_sb_refl {r s : ℕ} (a : Ix r s) : sameBlock a a := by
  cases a <;> trivial

theorem star_th {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (d0 : ℕ) (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    StarK (thAct p q r s c τ) ((homog (Ix p q × Ix r s) d0).map (thMkC p q r s c))
      ((casW (fun x => La x + τ0) : ℚ) : ℝ) := by
  intro t ht x hx hcas
  let Y : Submodule ℂ (Pol p q r s) :=
    harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2)
  haveI : FiniteDimensional ℂ (homog (Ix p q × Ix r s) (d0 + 2)) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ ℂ (d0 + 2))
  haveI : FiniteDimensional ℂ Y :=
    Submodule.finiteDimensional_of_le (S₂ := homog (Ix p q × Ix r s) (d0 + 2)) inf_le_right
  have hYK : KSt (units (fockAct2 p q r s)) Y := fun a b hab y hy =>
    ⟨⟨harmonic_stable_second_action a b hab y hy.1.1, polChi_stable_second_action c _ hy.1.2⟩, homogeneous_stable_second_action (d0 + 2) a b hab y hy.2⟩
  have hYT : KSt (units (twAct p q r s τ)) Y := by
    intro a b hab y hy
    rw [star_tw]
    exact Y.add_mem (hYK a b hab y hy) (Y.smul_mem _ hy)
  have hgl : GlK (units (twAct p q r s τ)) := glK_of_lie (lie_tw p q r s τ)

  have hx1 : x ∈ (homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, b, hab, _, ⟨g, hg, rfl⟩, rfl⟩
    have hne : a ≠ b := by
      rintro rfl
      exact hab (star_sb_refl a)
    have hlow : thMkC p q r s c (PI.FockOneDegW.lowOp (p := p) (q := q) a b g) = 0 := by
      by_cases h2 : d0 < 2
      · rw [low_homog_small a b h2 hg, map_zero]
      · obtain ⟨e, rfl⟩ : ∃ e, d0 = e + 2 := ⟨d0 - 2, by omega⟩
        refine th_small c c0 hc e ?_ (low_homog a b hg)
        rw [← hd]; push_cast; linarith
    refine ⟨_, second_action_add_lowering hab hg, ?_⟩
    rw [map_add (f := _), hlow, add_zero, thAct_mk, twAct_apply, star_trace, if_neg hne]
    simp
  obtain ⟨y, hy, rfl⟩ := th_next c c0 hc d0 hd hx1
  let D : Module.End ℂ (Pol p q r s) := casK (units (twAct p q r s τ)) - (t : ℂ) • 1
  have hD : ∀ g, D g = casK (units (twAct p q r s τ)) g - (t : ℂ) • g := fun g => rfl
  refine star_inj_quot D (casK (units (thAct p q r s c τ)) - (t : ℂ) • 1) (thMkC p q r s c) ?_ Y ?_ ?_ hy ?_
  · intro g
    rw [hD, map_sub, map_smul, ← star_cas_mk]
    rfl
  · intro g hg
    rw [hD]
    exact Y.sub_mem (star_casK_mem hYT hg) (Y.smul_mem _ hg)
  · intro g0 hg0 hDg0
    by_contra hne
    let U : Submodule ℂ (Pol p q r s) := Y ⊓ LinearMap.ker D
    haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
    have hU0 : U ≠ ⊥ := by
      intro h
      have : g0 ∈ U := ⟨hg0, hDg0⟩
      rw [h] at this
      exact hne ((Submodule.mem_bot ℂ).1 this)
    have hUT : KSt (units (twAct p q r s τ)) U := by
      intro a b hab u hu
      refine ⟨hYT a b hab u hu.1, ?_⟩
      have h1 : D u = 0 := hu.2
      have h2 := LinearMap.congr_fun (cas_comm hgl hab) u
      simp only [Module.End.mul_apply] at h2
      show D _ = 0
      rw [hD] at h1 ⊢
      rw [h2, ← map_smul, ← map_sub, h1, map_zero]
    have hUK : KSt (units (fockAct2 p q r s)) U := by
      intro a b hab u hu
      have h1 := U.sub_mem (hUT a b hab u hu) (U.smul_mem (if a = b then τ else 0) hu)
      rw [star_tw, add_sub_cancel_right] at h1
      exact h1
    obtain ⟨ν, g, hgU, hw⟩ := hwExist2 U hU0 hUK
    obtain ⟨⟨a, b, hab, hroot⟩, hdeg⟩ := root_of_hw c c0 hc La hC.2.1 d0 hd hgU.1 hw
    have hlt := hC.2.2 ν a b hab hroot (dom2 hw) (supp2 hw) hdeg
    have hK := hwK_of_hwSub.1 hw.2
    have hKT : HwK (units (twAct p q r s τ)) (fun x => ν x + τ0) g := by
      refine ⟨fun a => ?_, fun a b h => ?_⟩
      · rw [star_tw, hK.1 a, if_pos rfl, hτ, ← add_smul]
        push_cast; rfl
      · rw [star_tw, hK.2 a b h, if_neg (PI.FockOneDegW.Core.posC_ne a b h)]
        simp
    have h1 : D g = 0 := hgU.2
    rw [hD, cas_hw hgl hKT, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have h2 : ((casW (fun x => ν x + τ0) : ℚ) : ℝ) = t := by
        have h3 : (((casW (fun x => ν x + τ0) : ℚ) : ℝ) : ℂ) = (t : ℂ) := by
          rw [← sub_eq_zero.1 h1]; simp
        exact_mod_cast h3
      have h4 : ((casW (fun x => La x + τ0) : ℚ) : ℝ) + ((r : ℝ) + s) <
          ((casW (fun x => ν x + τ0) : ℚ) : ℝ) := by exact_mod_cast hlt
      linarith
    · exact hw.1 h1
  · show casK (units (thAct p q r s c τ)) _ - (t : ℂ) • _ = 0
    exact sub_eq_zero.2 hcas

end PositivityTheory.KReal

end
end
end

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSide

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

namespace GoodSideLattices

variable {p q r s : ℕ}

theorem sd_trace_Eab (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h
    simp [Matrix.trace]
  · simp [Matrix.trace, Matrix.single, h, Ne.symm h]

theorem sd_sb_trans {a b c : Ix r s} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

theorem sd_sb_symm {a b : Ix r s} (h1 : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sd_sb_refl (a : Ix r s) : sameBlock a a := by
  rcases a with a | a <;> simp [sameBlock]

def sd_hA (p q r s d : ℕ) : Submodule ℂ (FV p q r s) := homog (Ix p q × Ix r s) d

instance sd_hA_fd (d : ℕ) : FiniteDimensional ℂ (sd_hA p q r s d) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (Ix p q × Ix r s) ℂ d)

def sd_fvTw (p q r s : ℕ) (τ : ℂ) : Mat r s →ₗ[ℂ] Module.End ℂ (FV p q r s) := twAct p q r s τ

theorem sd_fvTw_apply (τ : ℂ) (W : Mat r s) (u : FV p q r s) :
    sd_fvTw p q r s τ W u = fvAct2 p q r s W u + (τ * W.trace) • u :=
  twAct_apply p q r s τ W u

private theorem isHomogeneous_X_mul_pderiv {σ : Type} (i j : σ) {n : ℕ} {φ : MvPolynomial σ ℂ}
    (h : φ.IsHomogeneous n) : (X i * pderiv j φ).IsHomogeneous n := by
  have e : X i * pderiv j φ = pderiv j (X i * φ) - pderiv j (X i) * φ := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, ← mem_homogeneousSubmodule]
  refine Submodule.sub_mem _ ?_ ?_
  · rw [mem_homogeneousSubmodule]
    simpa using ((isHomogeneous_X (R := ℂ) i).mul h).pderiv (i := j)
  · rw [mem_homogeneousSubmodule]
    by_cases hij : j = i
    · subst hij
      simpa using h
    · rw [pderiv_X_of_ne (Ne.symm hij), zero_mul]
      exact isHomogeneous_zero _ _ _

private theorem omE_mem_homogeneousSubmodule_of_sameBlock {d : ℕ} (i : Ix p q) {a b : Ix r s} (hab : sameBlock a b)
    {x : Pol p q r s} (hx : x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d) :
    omE (i, a) (i, b) x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
  have hl : linePos (i, a) = linePos (i, b) := by
    rcases i with i | i <;> rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, linePos]
  rw [mem_homogeneousSubmodule] at hx
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply]
  refine Submodule.add_mem _ ?_ ?_
  · simp only [raiB, lowB, ← hl]
    split_ifs with h
    · rw [LinearMap.mulLeft_apply, mem_homogeneousSubmodule]
      exact isHomogeneous_X_mul_pderiv _ _ hx
    · rw [LinearMap.neg_apply, LinearMap.mulLeft_apply]
      refine Submodule.neg_mem _ ?_
      rw [mem_homogeneousSubmodule]
      simpa using ((isHomogeneous_X (R := ℂ) (i, b)).mul hx).pderiv (i := (i, a))
  · split_ifs
    · exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hx)
    · exact Submodule.zero_mem _

theorem sd_fvTw_mem (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) :
    ∀ x ∈ sd_hA p q r s d, sd_fvTw p q r s τ (Eab a b) x ∈ sd_hA p q r s d := by
  intro x hx
  rw [sd_fvTw_apply]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hx)
  have e := fockAct2_unit (p := p) (q := q) a b (show Pol p q r s from x)
  have key : (fockAct2 p q r s (Eab a b)) (show Pol p q r s from x) ∈
      homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
    rw [e]
    exact Submodule.sum_mem _ (fun i _ => omE_mem_homogeneousSubmodule_of_sameBlock i hab hx)
  exact key

def sd_rhoA (p q r s : ℕ) (τ : ℂ) (d : ℕ) (a b : Ix r s) : Module.End ℂ (sd_hA p q r s d) :=
  if h : sameBlock a b then (sd_fvTw p q r s τ (Eab a b)).restrict (sd_fvTw_mem τ d h) else 0

theorem sd_rhoA_coe (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) (u : sd_hA p q r s d) :
    (sd_rhoA p q r s τ d a b u : FV p q r s) = sd_fvTw p q r s τ (Eab a b) u := by
  unfold sd_rhoA
  rw [dite_eq_left hab]
  rfl

theorem sd_rhoA_adj (τ : ℂ) (τ0 : ℚ) (hτ : τ = τ0) (d : ℕ) : AdjK (sd_rhoA p q r s τ d) := by
  intro a b hab u v
  rw [Submodule.coe_inner, Submodule.coe_inner, sd_rhoA_coe τ d hab,
    sd_rhoA_coe τ d (sd_sb_symm hab), sd_fvTw_apply, sd_fvTw_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adj2 p q r s a b, sd_trace_Eab,
    sd_trace_Eab]
  by_cases h : a = b
  · subst h
    simp [epsB, hab, hτ]
  · simp [epsB, hab, hτ, h, Ne.symm h]

private theorem Eab_mul_Eab (a b c e : Ix r s) :
    Eab a b * Eab c e = if b = c then Eab a e else 0 := by
  unfold Eab
  split_ifs with h
  · subst h
    simp
  · simp [h]

theorem sd_rhoA_gl (τ : ℂ) (d : ℕ) : GlK (sd_rhoA p q r s τ d) := by
  intro a b c e hab hce
  have hM : Eab a b * Eab c e - Eab c e * Eab a b =
      (if b = c then Eab a e else 0) - (if e = a then Eab c b else 0) := by
    rw [Eab_mul_Eab, Eab_mul_Eab]
  have hL : IsLie (sd_fvTw p q r s τ) := lie_tw p q r s τ
  have hu : ∀ u : FV p q r s,
      sd_fvTw p q r s τ (Eab a b) (sd_fvTw p q r s τ (Eab c e) u) -
        sd_fvTw p q r s τ (Eab c e) (sd_fvTw p q r s τ (Eab a b) u) =
      sd_fvTw p q r s τ ((if b = c then Eab a e else 0) - (if e = a then Eab c b else 0)) u := by
    intro u
    rw [← hM, ← hL]
    rfl
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply,
    sd_rhoA_coe τ d hab, sd_rhoA_coe τ d hce, sd_rhoA_coe τ d hce, sd_rhoA_coe τ d hab, hu]
  have s1 : b = c → sameBlock a e := fun h1 => sd_sb_trans hab (by rw [h1]; exact hce)
  have s2 : e = a → sameBlock c b := fun h2 => sd_sb_trans hce (by rw [h2]; exact hab)
  split_ifs with h1 h2 h2
  · rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub,
      sd_rhoA_coe τ d (s1 h1), sd_rhoA_coe τ d (s2 h2)]
  · rw [sub_zero, sub_zero, sd_rhoA_coe τ d (s1 h1)]
  · rw [zero_sub, zero_sub, map_neg, LinearMap.neg_apply, LinearMap.neg_apply,
      Submodule.coe_neg, sd_rhoA_coe τ d (s2 h2)]
  · simp

def sd_fvMk (p q r s : ℕ) (c : ℂ) : FV p q r s →ₗ[ℂ] ThC p q r s c := thMkC p q r s c

theorem sd_mem_genG {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genG act S ∧ ∀ W, ∀ x ∈ genG act S, act W x ∈ genG act S := by
  refine ⟨fun x hx => ?_, fun W x hx => ?_⟩
  · exact Submodule.mem_sInf.2 (fun N hN => hN.1 hx)
  · rw [genG, Submodule.mem_sInf] at hx ⊢
    intro N hN
    exact hN.2 W x (hx N hN)

end GoodSideLattices

open GoodSideLattices in
theorem side_of {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (hN : Nontrivial (ThC p q r s c)) :
    Side (fun x => La x + τ0) (ThC p q r s c) (thAct p q r s c τ) := by
  obtain ⟨d0, f0, hd0, hf0, hhw, hmin⟩ := exists_gen c c0 hc La hC.1 hC.2.1
  have hne : ∀ a b : Ix r s, posC a b → a ≠ b := by
    rintro a b h rfl
    rcases a with a | a <;> simp [posC] at h
  let f : sd_hA p q r s d0 := ⟨f0, hf0⟩
  let ι : sd_hA p q r s d0 →ₗ[ℂ] ThC p q r s c := (sd_fvMk p q r s c).comp (sd_hA p q r s d0).subtype
  have hι : ∀ u : sd_hA p q r s d0, ι u = thMkC p q r s c (show Pol p q r s from (u : FV p q r s)) :=
    fun u => rfl
  refine ⟨lie_th p q r s c τ, hN, sd_hA p q r s d0, inferInstance, inferInstance, inferInstance,
    sd_rhoA p q r s τ d0, ι, f, sd_rhoA_adj τ τ0 hτ d0, sd_rhoA_gl τ d0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    rw [sd_rhoA_coe τ d0 (sd_sb_refl a), sd_fvTw_apply, sd_trace_Eab, if_pos rfl]
    have h1 : fvAct2 p q r s (Eab a a) (f : FV p q r s) = ((La a : ℚ) : ℂ) • (f : FV p q r s) :=
      hhw.1 a
    rw [h1, Submodule.coe_smul, hτ]
    push_cast
    rw [mul_one, add_smul]
  · intro a b hab
    by_cases hs : sameBlock a b
    · apply Subtype.ext
      rw [sd_rhoA_coe τ d0 hs, sd_fvTw_apply, sd_trace_Eab, if_neg (hne a b hab)]
      have h1 : fvAct2 p q r s (Eab a b) (f : FV p q r s) = 0 := hhw.2 a b hab
      rw [h1]
      simp
    · simp [sd_rhoA, hs]
  · intro a b hab u
    rw [hι, hι, thAct_mk, sd_rhoA_coe τ d0 hab]
    rfl
  · set N := genG (thAct p q r s c τ) (ℂ ∙ ι f) with hNdef
    have hst := (sd_mem_genG (thAct p q r s c τ) (ℂ ∙ ι f)).2
    refine th_gen_harm c τ c0 hc N ?_ hst
    rw [Submodule.map_le_iff_le_comap]
    apply hmin
    · show thMkC p q r s c f0 ∈ N
      exact (sd_mem_genG (thAct p q r s c τ) (ℂ ∙ ι f)).1 (Submodule.mem_span_singleton_self _)
    · intro a b _ x hx
      rw [Submodule.mem_comap] at hx ⊢
      have e : thMkC p q r s c (units (fockAct2 p q r s) a b x) =
          thAct p q r s c τ (Eab a b) (thMkC p q r s c x) -
            (τ * (Eab a b).trace) • thMkC p q r s c x := by
        rw [thAct_mk, twAct_apply, map_add (f := _), map_smul]
        simp [units]
      rw [e]
      exact N.sub_mem (hst _ _ hx) (N.smul_mem _ hx)
  · have e : LinearMap.range ι = Submodule.map (thMkC p q r s c) (homog (Ix p q × Ix r s) d0) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [e]
    exact star_th c τ c0 τ0 hc hτ La hC d0 hd0

end PositivityTheory.KReal

end
end
end
