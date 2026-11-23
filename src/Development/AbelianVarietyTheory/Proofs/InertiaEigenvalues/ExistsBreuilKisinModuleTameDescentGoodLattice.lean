module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDescentDatumAndStableStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModuleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLOfEPowSmulMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersSubsetTameType

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatum

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizXi

section General

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι]


omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in
theorem desc_succ_eq_zero {P : PhiMod O K l e a ι} (D : Conn P) {v : Vec K a ι} (hv : D.N v = 0) (i : ℕ) :
    D.desc (i + 1) v = 0 := by
  induction i with
  | zero => simp [Conn.desc_succ, Conn.desc_zero, hv]
  | succ i ih => rw [Conn.desc_succ, hv, zero_sub, map_neg, map_nsmul, ih, smul_zero, neg_zero]

theorem muDiv_zero (g : ↥(GK (ϖ.field a))) : ϖ.muDiv a O g 0 = 1 := by
  simp only [PiSys.muDiv, dpow_zero]
  rfl

theorem taylor_fix (g : ↥(GK (ϖ.field a))) {P : PhiMod O K l e a ι} (D : Conn P) (Γ : Matrix ι ι (OA l O))
    (m : P.MM) (hm : D.N m.1 = 0)
    (h : ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ z : ι → OCr l O,
      (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) -
        ∑ i ∈ Finset.range n, ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ =
          (l : OCr l O) ^ r • z) :
    (Γ.map (toOCr l O) *ᵥ fun i => galOCr O g (toCris t ϖ P m i)) = toCris t ϖ P m := by
  have hsum : ∀ n, ∑ i ∈ Finset.range (n + 1),
      ϖ.muDiv a O g i • toCris t ϖ P ⟨D.desc i m, D.desc_mem i m.2⟩ = toCris t ϖ P m := by
    intro n
    rw [Finset.sum_range_succ']
    have h0 : ∀ i ∈ Finset.range n, ϖ.muDiv a O g (i + 1) •
        toCris t ϖ P ⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ = 0 := by
      intro i _
      have : (⟨D.desc (i + 1) m, D.desc_mem (i + 1) m.2⟩ : P.MM) = 0 :=
        Subtype.ext (desc_succ_eq_zero D hm i)
      rw [this, map_zero, smul_zero]
    rw [Finset.sum_eq_zero h0, zero_add, muDiv_zero, one_smul]
    exact congrArg _ (Subtype.ext (D.desc_zero m))
  funext i
  rw [← sub_eq_zero]
  refine sep_OCr _ fun r => ?_
  obtain ⟨n₀, hn₀⟩ := h r
  obtain ⟨z, hz⟩ := hn₀ (n₀ + 1) (Nat.le_succ _)
  rw [hsum] at hz
  exact ⟨z i, by rw [← Pi.sub_apply, hz, Pi.smul_apply, smul_eq_mul]⟩

theorem toBcris_eq_toOB {P : PhiMod O K l e a ι} (m : P.MMl) (hm : m.1 ∈ P.MM) (i : ι) :
    toBcris t ϖ P m i = toOB l O (toCris t ϖ P ⟨m.1, hm⟩ i) := by
  rw [toBcris_apply, toCris_apply, ← ϖ.iB_of_mem t K]
  rfl

theorem exists_pow_smul_mem_MM {P : PhiMod O K l e a ι} (m : P.MMl) :
    ∃ N : ℕ, (((l ^ N : ℕ) • m : P.MMl) : Vec K a ι) ∈ P.MM := by
  have hc : ∀ τ i, ∃ n : ℕ, ((l : S O K e) : K⟦X⟧) ^ n * (P.mxInv τ *ᵥ m.1 τ) i ∈ S O K e :=
    fun τ i => mem_away.1 (P.mem_extc_iff.1 (mem_tot.1 m.2 τ) i)
  choose n hn using hc
  refine ⟨∑ τ, ∑ i, n τ i, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_⟩
  have hle : n τ i ≤ ∑ τ, ∑ i, n τ i :=
    (Finset.single_le_sum (f := fun i => n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, n τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  have h1 : ((((l ^ (∑ τ, ∑ i, n τ i) : ℕ) • m : P.MMl) : Vec K a ι)) τ =
      ((l : S O K e) : K⟦X⟧) ^ (∑ τ, ∑ i, n τ i) • m.1 τ := by
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul K⟦X⟧]
    simp
  rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (S O K e).mul_mem ((S O K e).pow_mem (SetLike.coe_mem _) _) (hn τ i)

theorem actB_smul {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : OB l O) (z : TW (OB l O) T) : actB s T g (r • z) = galOB O (s g) r • actB s T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x =>
    simp only [actB, TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable [TameDescentExponentData K l e a]

theorem actB_jB {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (y : ι → OB l O) :
    actB (sQ l) T g (jB y) = jB (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (y i)) := by
  obtain ⟨-, hI⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι P T I
  obtain ⟨-, huniq, -, -, hgal⟩ := hI jB hjB
  have hstab := (I.exists_isLMat_iff (sQ l g) g).1 ⟨Γ, hΓ⟩
  have hval : ∀ c : ι → OA l O, IsCrisVal t ϖ P jB (inclL t ϖ P c) (jB fun i => toB l O (c i)) :=
    fun c => ⟨1, c, by simp, by simp, by simp⟩
  have hbas : ∀ j, actB (sQ l) T g (jB (Pi.single j 1)) = jB (Γ.map (toB l O) *ᵥ Pi.single j 1) := by
    intro j
    have e1 : (Pi.single j 1 : ι → OB l O) = fun i => toB l O ((Pi.single j 1 : ι → OA l O) i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have e2 : (Γ.map (toB l O) *ᵥ Pi.single j 1) = fun i => toB l O
        ((Γ *ᵥ fun k => galOA O (sQ l g) ((Pi.single j 1 : ι → OA l O) k)) i) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite (galOA O (sQ l g)), apply_ite (toB l O)]
    have h1 := hgal g hstab _ _ (hval (Pi.single j 1))
    rw [hΓ] at h1
    rw [e2, e1]
    exact huniq _ _ _ h1 (hval _)
  conv_lhs => rw [pi_eq_sum_univ' y]

  rw [map_sum, map_sum]
  conv_rhs => rw [pi_eq_sum_univ' (fun i => galOB O (sQ l g) (y i))]

  rw [← Matrix.mulVecLin_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearEquiv.map_smul, actB_smul, hbas, map_smul, Matrix.mulVecLin_apply, LinearEquiv.map_smul]

theorem horiz_of_fix {P : PhiMod O K l e a ι} {T : LocLat (Gl l) ℚ_[l] K O} (I : Ident t ϖ P T)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (hjB : IsCrisCmp I jB) (g : Gl l)
    (Γ : Matrix ι ι (OA l O)) (hΓ : I.IsLMat (sQ l g) g Γ) (ξ : P.MMl) (N : ℕ)
    (hN : (((l ^ N : ℕ) • ξ : P.MMl) : Vec K a ι) ∈ P.MM)
    (hfix : (Γ.map (toOCr l O) *ᵥ fun i => galOCr O (sQ l g) (toCris t ϖ P ⟨_, hN⟩ i)) =
      toCris t ϖ P ⟨_, hN⟩) :
    actB (sQ l) T g (jB (toBcris t ϖ P ξ)) = jB (toBcris t ϖ P ξ) := by
  have hB : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ((l ^ N : ℕ) • ξ) i)) =
      toBcris t ϖ P ((l ^ N : ℕ) • ξ) := by
    funext i
    rw [toBcris_eq_toOB t ϖ _ hN i, ← hfix]

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, toBcris_eq_toOB t ϖ _ hN, galOB_toOB,
    Matrix.map_apply, toB, AlgHom.comp_apply]
  rw [map_nsmul] at hB
  have hu : IsUnit ((l ^ N : ℕ) : OB l O) := by
    rw [Nat.cast_pow]; exact isUnit_l_OB.pow N
  have hg : (fun i => galOB O (sQ l g) (((l ^ N : ℕ) • toBcris t ϖ P ξ) i)) =
      (l ^ N : ℕ) • fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [hg, Matrix.mulVec_smul] at hB
  have hfx : (Γ.map (toB l O) *ᵥ fun i => galOB O (sQ l g) (toBcris t ϖ P ξ i)) = toBcris t ϖ P ξ := by
    funext i
    have h3 := congrFun hB i
    simp only [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (OB l O), smul_eq_mul] at h3
    exact hu.mul_left_cancel h3
  rw [actB_jB t ϖ I jB hjB g Γ hΓ _, hfx]

end General

end GlobalTheory.HorizXi

namespace GlobalTheory.HorizXi

theorem galois_fixes_xi : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB hjB C hC hTay g hg d hξ
  have h1 := hTay ⟨sQ l g, hg⟩
  obtain ⟨Γ, h2⟩ := h1
  have h3 := exists_pow_smul_mem_MM (⟨P.xi d, hξ⟩ : P.MMl)
  obtain ⟨N, hN⟩ := h3
  have hNm : C.N (((l ^ N : ℕ) • (⟨P.xi d, hξ⟩ : P.MMl) : P.MMl) : Vec _ a ι) = 0 := by
    rw [Submodule.coe_smul_of_tower, map_nsmul, Conn.N_apply, hC, PhiMod.nabla_xi, smul_zero, smul_zero]
  exact horiz_of_fix (thetaW a LL) ϖ I jB hjB g Γ h2.1 _ N hN
    (taylor_fix (thetaW a LL) ϖ ⟨sQ l g, hg⟩ C Γ ⟨_, hN⟩ hNm (h2.2 ⟨_, hN⟩))

end GlobalTheory.HorizXi
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatumStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_fixes_crystalline_image_descentDatum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T), IsCrisCmp I jB → ∀ C : Conn P, C.nabla = P.nabla → Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C → IsHoriz (thetaW a LL) ϖ (sQ l) P jB := by
  first | exact @GlobalTheory.HorizXi.galois_fixes_xi | exact GlobalTheory.HorizXi.galois_fixes_xi | (intros; apply GlobalTheory.HorizXi.galois_fixes_xi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisinStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∃ C : Conn P, C.nabla = P.nabla ∧ Ident.Taylor (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) C := by
  first | exact @GlobalTheory.IntConnTaylor.main | exact GlobalTheory.IntConnTaylor.main | (intros; apply GlobalTheory.IntConnTaylor.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphismStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

theorem _root_.GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ) (I : Ident t ϖ P T) (I' : Ident t ϖ Q T'), IsBK I → IsBK I' → ∀ f : LatHom T.L T'.L, ∃ F, IsMapOf I I' f F := by
  first | exact @GlobalTheory.BKReal.Full.main | exact GlobalTheory.BKReal.Full.main | (intros; apply GlobalTheory.BKReal.Full.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

theorem _root_.GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (T : Lat a O K ϖ), (letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) → Nonempty (BKMod t ϖ T) := by
  first | exact @GlobalTheory.BKReal.OfCrystal.main | exact GlobalTheory.BKReal.OfCrystal.main | (intros; apply GlobalTheory.BKReal.OfCrystal.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCrysBKFunctorOLOfBhattScholze

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

namespace GlobalTheory

theorem nonempty_crysBKFunctorOL_of_bhattScholze :
    GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → Nonempty (CrysBKFunctorOL a ϖ LL P) := by
  intro BS l _ a e _ _ ϖ LL _ P AI h
  refine ⟨BKFunctor.ofExists (fun T hT => GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal BS l a e _ _ _ ϖ T ?_) fun M M' f => GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism BS l a e _ _ _ ϖ _ _ _ _ _ _ M.I M'.I M.isBK M'.isBK f⟩
  obtain ⟨E, j, H⟩ := (BS l _ _ _ (isAinf_ainfObj (ϖ.field a))).1 P AI h LL T hT
  exact ⟨E, j, H⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersSubsetTameTypeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tameInertiaCharacters_subset_tameType : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Δ : Descent P) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → IsGalDesc (sQ l) I Δ → ∀ Sig : Finset (ZMod e), TameType a ϖ Pl T Sig → ∀ τ, Δ.chars τ ⊆ (Sig : Set (ZMod e)) := by
  first | exact @GlobalTheory.CharsDesc.chars_subset_sig | exact GlobalTheory.CharsDesc.chars_subset_sig | (intros; apply GlobalTheory.CharsDesc.chars_subset_sig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem exists_pack_isOfType : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), (∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H) → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∃ Pk : Pack a ϖ η H T, Pk.D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) := by
  intro hBS hF l _ a e _ _ ϖ LL _ _ hl Pl AI hstd η H Sig U hU T hT
  obtain ⟨F⟩ := GlobalTheory.nonempty_crysBKFunctorOL_of_bhattScholze hBS l a e ϖ LL Pl AI hstd
  let B := F.obj (resF T (ϖ.field a)) hT.crys
  let I : Ident (thetaW a LL) ϖ B.P T := Ident.ofRes B.I
  have hBK : IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) :=
    B.isBK
  obtain ⟨C, hC, hTay⟩ := GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin hBS l a e ϖ LL hl (Fin B.n) B.P T I hBK
  obtain ⟨⟨jB, hcmp⟩, -⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (Fin B.n) B.P T I
  have hhor := GlobalTheory.T.galois_fixes_crystalline_image_descentDatum l a e ϖ LL hl (Fin B.n) B.P T I jB hcmp C hC hTay
  obtain ⟨hst, hinf⟩ := GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed l a e ϖ LL (Fin B.n) B.P T I hBK
  have hK7 := GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule hBS l a e ϖ LL (Fin B.n) B.P T I hBK
  obtain ⟨⟨Δ, hΔ⟩, hLA⟩ := GlobalTheory.T.exists_galoisDescentDatum_and_stable l a e ϖ LL (Fin B.n) B.P T I hinf hK7
  obtain ⟨hEN, hjU⟩ := GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps hF l a e ϖ LL hl (Fin B.n) B.P T I jB Pl AI hstd hcmp hhor
  have hj : B.P.jumps ⊆ (U : Set ℤ) := hjU _ hT.jumps
  have hIcc : B.P.jumps ⊆ Set.Icc (-(η : ℤ)) H := fun i hi => hU i (hj hi)
  obtain ⟨hlow, hup⟩ := (GlobalTheory.BK.PhiMod.jumps_subset_Icc_iff _ _ l e a (Fin B.n) B.P η H).1 hIcc
  have hch := GlobalTheory.T.tameInertiaCharacters_subset_tameType l a e ϖ LL hl (Fin B.n) B.P T I jB Δ Pl AI hstd hcmp hhor hΔ Sig hT.type
  let D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin B.n) η H :=
    { toPhiMod := B.P
      desc := Δ
      nabla_mem := fun m hm => hC ▸ C.mem_MM m hm
      EN_mem := hEN
      lower := hlow
      upper := hup }
  let R : GalDat (thetaW a LL) ϖ (sQ l) D T :=
    { I := I
      jB := jB
      cmp := hcmp
      desc := hΔ
      stable := hLA hst
      horiz := hhor }
  exact ⟨⟨B.n, D, R, hBK⟩, ⟨hch, hj⟩⟩

end GlobalTheory.BKGal
end
end
