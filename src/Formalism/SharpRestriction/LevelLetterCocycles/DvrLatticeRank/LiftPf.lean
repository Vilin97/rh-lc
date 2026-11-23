module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalFormOfThreeInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfB

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem fix_of_mem_GK {K : FinExt l} {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ K.1) :
    σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

theorem Ks_stable (K : FinExt l) {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ Ks K 1) :
    σ x ∈ Ks K 1 := by
  have hle : Ks K 1 ≤ (Ks K 1).map (σ.symm : Om l ≃ₐ[ℚ_[l]] Om l).toAlgHom := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      refine (IntermediateField.mem_map _).2 ⟨y, (le_sup_left : K0 K ≤ _) hy, ?_⟩
      have h1 : σ y = y := fix_of_mem_GK hσ (inf_le_left (a := K.1) (b := MaximalUnramifiedExtension l) hy)
      show σ.symm y = y
      rw [AlgEquiv.symm_apply_eq]
      exact h1.symm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      refine (IntermediateField.mem_map _).2 ⟨σ y, ?_, by simp⟩
      apply (le_sup_right : _ ≤ K0 K ⊔ _)
      apply IntermediateField.subset_adjoin
      show (σ y) ^ (l ^ 1) = 1
      rw [← map_pow, show y ^ (l ^ 1) = 1 from hy, map_one]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 (hle hx)
  have hyx' : σ.symm y = x := hyx
  rw [← hyx', AlgEquiv.apply_symm_apply]
  exact hy

theorem GKin_normal (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) : (GKin hKK).Normal := by
  constructor
  intro n hn g
  rw [GKin, Subgroup.mem_subgroupOf] at hn ⊢
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have h1 : ((g : GQ l)⁻¹) x ∈ Ks K 1 := Ks_stable K (inv_mem g.2) hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem range_inclusion_eq (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) (hle : GK (cycL K) ≤ GK K) :
    (Subgroup.inclusion hle).range = GKin hKK := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 y.2
  · intro hx
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

theorem chi_cong (P : LocPrime l) (K : FinExt l) (g : GQ l) (hg : g ∈ GK (cycL K)) :
    ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
  have hp : l.Prime := Fact.out
  have hζl : P.ζQ 1 ^ (l ^ 1) = 1 := by
    have := P.ζQ_succ 0
    rw [P.ζQ_zero] at this
    simpa using this
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 (P.ζQ 1) hζl
  have hζK : P.ζQ 1 ∈ (cycL K).1 :=
    (le_sup_right : _ ≤ K0 K ⊔ _) (IntermediateField.subset_adjoin _ _ hζl)
  have hfix : g (P.ζQ 1) = P.ζQ 1 := fix_of_mem_GK hg hζK
  have hord : orderOf (P.ζQ 1) = l := orderOf_eq_prime (by simpa using hζl) P.ζQ_one
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      apply P.ζQ_one
      have h2 : P.ζQ 1 ^ 0 = P.ζQ 1 ^ 1 := by rw [pow_one, ← hga, hfix]
      rw [pow_zero, pow_one] at h2
      exact h2.symm
    · exact h
  have hζ0 : P.ζQ 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hp.pos 1).ne'] at hζl
    exact zero_ne_one hζl
  have h3 : P.ζQ 1 ^ (a - 1) = 1 := by
    have h4 : P.ζQ 1 ^ (a - 1) * P.ζQ 1 = 1 * P.ζQ 1 := by
      rw [← pow_succ, Nat.sub_add_cancel ha1, one_mul, ← hga, hfix]
    exact mul_right_cancel₀ hζ0 h4
  have hdvdN : l ∣ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have hdvdN1 : l ^ 1 ∣ a - 1 := by rw [pow_one]; exact hdvdN
  have hcast : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by omega
  have h1 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) 1).2
    (by rw [hcast]; exact_mod_cast hdvdN1)
  have e : (P.χQ g : ℚ_[l]) - 1 = ((P.χQ g : ℚ_[l]) - (a : ℚ_[l])) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
    push_cast; ring
  rw [e]
  refine ((Padic.nonarchimedean _ _).trans (max_le ha h1)).trans (le_of_eq ?_)
  simp

theorem v_ge_one (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (hx : ‖x‖ ≤ (l : ℝ)⁻¹) :
    (1 : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : ‖x / l‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos))]
    exact hx
  have hxy : x = (l : ℚ_[l]) * (x / l) := by field_simp
  have hyO : algebraMap ℚ_[l] ↥LL.1 (x / l) ∈ OL LL := by
    obtain ⟨y, hy'⟩ : ∃ y : ℤ_[l], (y : ℚ_[l]) = x / l := ⟨⟨x / l, hy⟩, rfl⟩
    rw [← hy', show (y : ℚ_[l]) = algebraMap ℤ_[l] ℚ_[l] y from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  rw [hxy, map_mul, map_natCast, AddValuation.map_mul, P.v_l LL]
  exact le_add_of_nonneg_right ((P.v_O LL _).2 hyO)

theorem FildR_succ_le (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    FildR (P.PD K) T.ρ τ (a + 1) ≤ FildR (P.PD K) T.ρ τ a := by
  unfold FildR FilV
  refine inf_le_inf_left _ ?_
  have hle : ((P.PD K).Fil (a + 1)).restrictScalars ℚ_[l] ≤ ((P.PD K).Fil a).restrictScalars ℚ_[l] :=
    fun x hx => (P.PD K).Fil_anti a hx
  rintro x ⟨y, rfl⟩
  exact ⟨TensorProduct.AlgebraTensorModule.map LinearMap.id (Submodule.inclusion hle) y, by
    rw [← LinearMap.comp_apply, ← TensorProduct.AlgebraTensorModule.map_comp]
    rfl⟩

theorem multV_ne_zero (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (hfd : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ)) (hj : IsJumpV (P.PD K) T.ρ τ a) :
    multV (P.PD K) T.ρ τ a ≠ 0 := by
  unfold multV
  have hle := FildR_succ_le P K LL T τ a
  have hlt : FildR (P.PD K) T.ρ τ (a + 1) < FildR (P.PD K) T.ρ τ a := lt_of_le_of_ne hle hj
  haveI := hfd
  haveI : FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T.ρ τ a) := Submodule.finiteDimensional_of_le inf_le_left
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem isJump_of_multV (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (h : multV (P.PD K) T.ρ τ a ≠ 0) : IsJumpV (P.PD K) T.ρ τ a := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPf

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.CyclotomicLifting

theorem padicValNat_le_of_dvd' (p : ℕ) {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b := by
  by_cases hp1 : p = 1
  · subst hp1
    first
      | simp
      | simp [padicValNat]
      | (unfold padicValNat; simp)
  · nth_rw 2 [Nat.padicValNat_def]
    have hd : p ^ padicValNat p a ∣ b := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hab
    have hf : FiniteMultiplicity p b := Nat.finiteMultiplicity_iff.2 ⟨hp1, Nat.pos_of_ne_zero hb⟩
    first
      | exact hf.le_multiplicity_of_pow_dvd hd
      | exact (hf.pow_dvd_iff_le_multiplicity).mp hd

theorem ePB_le_expLift_pf (l M H h : ℕ) (jumps : Finset ℤ) (hM : M ≤ h) (hH : H ≤ 2 * h) :
    Formalism.MainNotions.LiftingTheory.ePB l 1 M H jumps ≤ expLift l h (Formalism.MainNotions.LiftingTheory.JSet jumps M) := by
  unfold Formalism.MainNotions.LiftingTheory.ePB expLift LiftingTheory.eWB LIFT.eU
  have h1 : padicValNat l (2 * H).factorial ≤ padicValNat l (2 * (2 * h)).factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial (by omega)) (Nat.factorial_ne_zero _)
  have h2 : padicValNat l M.factorial ≤ padicValNat l h.factorial :=
    padicValNat_le_of_dvd' l (Nat.factorial_dvd_factorial hM) (Nat.factorial_ne_zero _)
  omega

theorem JSet_sub_pf (jumps : Finset ℤ) (M h : ℕ) (hj : ∀ a ∈ jumps, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hM : M ≤ h) :
    Formalism.MainNotions.LiftingTheory.JSet jumps M ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧
      (0 : ℤ) ∉ Formalism.MainNotions.LiftingTheory.JSet jumps M := by
  unfold Formalism.MainNotions.LiftingTheory.JSet
  constructor
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
      obtain ⟨ha1, ha2⟩ := hj _ ha
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro h0
    rcases Finset.mem_union.mp h0 with h0 | h0
    · exact (Finset.mem_filter.mp h0).2 rfl
    · have h1 := (Finset.mem_Icc.mp h0).1
      omega

theorem pow_smul_mem_of_le {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O M) (p : O) {e e' : ℕ} (he : e ≤ e') {c : M} (hc : p ^ e • c ∈ S) :
    p ^ e' • c ∈ S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact S.smul_mem _ hc

theorem jumpSet_bound {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (M h : ℕ) (hM : M ≤ h) : ∀ a ∈ Formalism.MainNotions.LiftingTheory.jumpSet W T M M, -(h : ℤ) ≤ a ∧ a ≤ h := by
  classical
  unfold Formalism.MainNotions.LiftingTheory.jumpSet
  intro a ha
  have ha' : a ∈ Finset.Icc (-(M : ℤ)) M := by
    first
      | exact Finset.mem_of_mem_filter a ha
      | (simp only [Finset.mem_filter] at ha; exact ha.1)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha'
  constructor <;> omega

theorem lift_jumps_bounded {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)
    {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (Fm : LatHom T₁.L T₂.L) (h n : ℕ)
    (Js : Finset ℤ) (hJb : ∀ a ∈ Js, -(h : ℤ) ≤ a ∧ a ≤ h)
    (hL : Fm.LiftF (P.PD K) (Formalism.MainNotions.LiftingTheory.ePB l 1 (Formalism.MainNotions.LiftingTheory.Mmax n fun _ => h)
      (Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) fun _ => h) Js)) :
    ∃ J : Finset ℤ, J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      Fm.LiftF (P.PD K) (expLift l h J) := by
  have hMm : Formalism.MainNotions.LiftingTheory.Mmax n (fun _ => h) ≤ h := by
    unfold Formalism.MainNotions.LiftingTheory.Mmax
    exact Finset.sup_le fun _ _ => le_rfl
  have hHm : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => h) (fun _ => h) ≤ 2 * h := by
    unfold Formalism.MainNotions.LiftingTheory.Hmax
    exact Finset.sup_le fun _ _ => by dsimp only; omega
  obtain ⟨hJ1, hJ2⟩ := JSet_sub_pf Js _ h hJb hMm
  refine ⟨_, hJ1, hJ2, ?_⟩
  have he := ePB_le_expLift_pf l _ _ h Js hMm hHm
  unfold Formalism.WeaklyAdmissibleFiltrations.LatHom.LiftF at hL ⊢
  intro c hc
  exact pow_smul_mem_of_le _ _ he (hL c hc)

theorem lift_bound_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) : liftR D := by
  obtain ⟨-, -, -, -, -, -, hA4, -, -, -, hA8, -, hA12⟩ := hA
  obtain ⟨-, -, -, -, hDesc⟩ := hA4
  intro l _ hl K LL hg T₁ T₂ Fm r S η m h up b hH
  have hKK : K.1 ≤ (cycL K).1 := hg.2.2.1
  have hle : GK (cycL K) ≤ GK K := GK_le hKK
  have hg1 : Good (cycL K) 1 LL := by
    refine ⟨le_rfl, fun h2 => absurd h2 hl, ?_, ?_⟩
    · rw [Ks_cycL K]; exact le_rfl
    · rw [Ks_cycL K]; exact hg.2.2.2
  have hD := hDesc l (cycL K) K hKK hle (GKin_normal K hKK) 1 LL hg1
  have hs : ((HW l).W (cycL K) 1 LL hg1).s = 1 := (HW l).W_s _ _ _ _
  have hCB : Formalism.MainNotions.LiftingTheory.CaseB ((HW l).W (cycL K) 1 LL hg1) := by
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff]
      intro g _
      rw [((HW l).W (cycL K) 1 LL hg1).GKs_def, hs, Nat.cast_one, (D.loc l).PD_χ,
        ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]
      exact v_ge_one _ LL _ (chi_cong (D.loc l) K g g.2)
    · rw [(D.loc l).PD_p, hs, finrank_cycL]
      simp
  have hv0 := hD.2 hCB rfl (by rw [max_unramified_cyclotomic_eq K]; exact inf_le_left)
  have hrange : (Subgroup.inclusion hle).range.Normal := by
    rw [range_inclusion_eq K hKK hle]
    exact GKin_normal K hKK
  have hres := hA12 l (cycL K) K hKK hle LL T₁ hH.1
  have hres2 := hA12 l (cycL K) K hKK hle LL T₂ hH.2.1
  have hL := (hD.1 hrange T₁ T₂ Fm (fun _ => h) (fun _ => h) ⟨hres.1, hres2.1, hH.2.2.1⟩
    (by
      intro i τ _ a ha
      have hm := multV_ne_zero (D.loc l) (cycL K) LL _ τ a ((hA8 l (cycL K) LL _).2 τ).1 ha
      rw [hres.2 τ a] at hm
      have := hH.2.2.2.2.2.2.2.1 (τ.comp (IntermediateField.inclusion hKK)) a
        (isJump_of_multV (D.loc l) K LL T₁ _ a hm)
      simpa using this)).2 hCB
  rw [(D.loc l).PD_p, hv0, add_zero, hs] at hL
  exact lift_jumps_bounded (D.loc l) K LL Fm h _ _
    (jumpSet_bound (D.loc l) (cycL K) LL _ _ _ h (Finset.sup_le fun _ _ => le_rfl)) hL

end Formalism.MainNotions.N.Ln34

end
end
end
