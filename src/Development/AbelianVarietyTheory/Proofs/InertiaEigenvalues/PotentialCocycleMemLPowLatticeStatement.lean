module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBoundStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowGaloisSubOneMemTensorAcrisImageStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensor

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisInt

theorem tw_incl_smul {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

theorem tw_incl_comp {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R R' R'' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R'']
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G Qp LL O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a t => simp [TWincl]

theorem mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hLM hML jB hcmp ε hε z
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hK := (GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hLM hML ε δ hε hδ).2.2.2
  have step1 : ∀ c : ι → OA l O, ∃ y : TW (OA l O) T,
      jB (fun i => toB l O (((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) * c i)) = TWincl (toB l O) T y := by
    intro c
    obtain ⟨y, hy⟩ := hK (inclL t ϖ P c) ⟨c, rfl⟩
    refine ⟨y, hcmp _ y ?_⟩
    rw [← hy]
    congr 1
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [map_mul, Algebra.TensorProduct.tmul_pow]
  choose y hy using fun i : ι => step1 (Pi.single i 1)
  refine ⟨∑ i, z i • TWincl (toOCr l O) T (y i), ?_⟩
  have hsingle : ∀ i, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (Pi.single i 1) =
      TWincl (toB l O) T (y i) := by
    intro i
    rw [← hy i, ← map_smul]
    congr 1
    funext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hz : (fun i => toOB l O (z i)) = ∑ i, toOB l O (z i) • (Pi.single i (1 : OB l O)) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]

  rw [hz, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, hsingle, tw_incl_smul, tw_incl_comp]
  rfl

end GlobalTheory.BKGal.CrisInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulAcrisLatticeMemAcrisTensorStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ ε : OCb l, IsEps ε → ∀ z : ι → OCr l O, ∃ w : TW (OCr l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ α) • jB (fun i => toOB l O (z i)) = TWincl (toOB l O) T w := by
  first | exact @GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | exact GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem | (intros; apply GlobalTheory.BKGal.CrisInt.mu_pow_smul_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMem

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMemStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  first | exact @GlobalTheory.BKGal.muPow_smul_actB_sub_mem | exact GlobalTheory.BKGal.muPow_smul_actB_sub_mem | (intros; apply GlobalTheory.BKGal.muPow_smul_actB_sub_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKExp

theorem muPow_smul_crisVal_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY hy m₀ b₀ hm hb ε hε
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hEM : y ∈ D.toPhiMod.EM η := hyY.1
  obtain ⟨-, hLA⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩ hEM m₀ hm
  obtain ⟨c, hc⟩ := hLA
  have hU := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  obtain ⟨z, hz⟩ := ((GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ).2.2.2) _ ⟨c, rfl⟩
  have hC := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := rfl
  have hpow : ∀ n : ℕ, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) = (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε)) ^ n := by
    intro n
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hunit : ∀ n : ℕ, IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
    intro n
    rw [hpow, e1]
    exact (hU.map (Algebra.TensorProduct.includeRight (R := ℤ_[l]) (A := O))).pow n
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)) with hmdef
  obtain ⟨u, hu⟩ := hunit (H + η)
  have hval : IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀)
      ((↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i))) := by
    refine ⟨m, c, ⟨u, hu⟩, hc.symm, ?_⟩
    rw [← hu, smul_smul, Units.mul_inv, one_smul]
  have hb0 := hC _ _ _ hb hval
  have hmain : toB l O m • b₀ = R.jB (fun i => toB l O (c i)) := by
    rw [hb0, ← hu, smul_smul, Units.mul_inv, one_smul]
  set c' : ι → OA l O := fun i => ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * c i with hc'
  have hL : inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) • inclL t ϖ D.toPhiMod c = inclL t ϖ D.toPhiMod c' := by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [hc', map_mul]
  rw [hL] at hz
  have hcmp := R.cmp c' z hz
  refine ⟨z, ?_⟩
  rw [← hcmp]
  have e2 : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) ^ (H + 2 * η) = ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * m := by
    rw [hmdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add, Algebra.TensorProduct.tmul_pow, one_pow]
    ring_nf
  have e3 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) = toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η)) * toB l O m := by
    first
    | rw [e2, map_mul]
    | rw [hmdef, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← pow_add]; ring_nf
  rw [e3, mul_smul, hmain, ← map_smul]
  congr 1
  funext i
  simp [hc', map_mul]

end GlobalTheory.BKExp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulCrystallineValueMemAinfLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O) (b₀ : TW (OB l O) T), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ → ∀ ε : OCb l, IsEps ε → ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η)) • b₀ = TWincl (toB l O) T z := by
  first | exact @GlobalTheory.BKExp.muPow_smul_crisVal_integral | exact GlobalTheory.BKExp.muPow_smul_crisVal_integral | (intros; apply GlobalTheory.BKExp.muPow_smul_crisVal_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.CocycleInt

theorem TWincl_comp_toB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] {T : LocLat (Gl l) ℚ_[l] K O} (z : TW (OA l O) T) :
    TWincl (toOB l O) T (TWincl (toOCr l O) T z) = TWincl (toB l O) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul r x => rfl

theorem TWincl_smul' {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a t => simp [TWincl, TensorProduct.smul_tmul']

end GlobalTheory.BKGal.CocycleInt


open GlobalTheory.BKGal.CocycleInt in
theorem GlobalTheory.BKGal.potential_cocycle_mem_lpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R hηH hl y hyY c hc b hb g hg hex
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hval, rfl⟩ := hb
  have hl2 : l ≠ 2 := by omega
  obtain ⟨z, hz⟩ := GlobalTheory.T.prime_pow_galois_sub_one_mem_tensorAcris_image l a e O K t ϖ hl2 ι η H D T R σ c (by rw [hconn]; exact hc) g hg
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.T.mu_pow_smul_acrisLattice_mem_acrisTensor l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower R.jB R.cmp ε hε z
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.muPow_smul_crystallineValue_mem_ainfLattice l a e O K t ϖ ι η H D T R y hyY hy m₀ b₀ hm₀ hval ε hε
  obtain ⟨z₁, hz₁⟩ := GlobalTheory.T.muOf_pow_smul_actB_sub_self_mem_range_TWincl l O K T g ε hε (H + 2 * η) b₀ z₀ hz₀
  obtain ⟨n, x, hx⟩ := hex
  set jσ := R.jB (toBcris t ϖ D.toPhiMod σ)
  refine GlobalTheory.T.pow_smul_mem_lattice_of_acris_bound l O K T hl2 ε hε (H + 2 * η) n c (by omega) _ x
    (toOCr l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) • w₁ - (l : O) ^ c • TWincl (toOCr l O) T z₁) hx ?_
  have hsplit : actB (sQ l) T g (jσ - b₀) - (jσ - b₀) = (actB (sQ l) T g jσ - jσ) - (actB (sQ l) T g b₀ - b₀) := by
    rw [map_sub]; abel
  have hmu : ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + 2 * η) : OA l O) =
      ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ (H + η)) * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ η) := by
    rw [show H + 2 * η = (H + η) + η by ring, pow_add]
  rw [hsplit, map_sub, TWincl_smul', map_smul, TWincl_comp_toB, ← hz₁, smul_sub, hz, ← hw₁]
  rw [smul_sub, hmu, map_mul, mul_smul, hw₁, smul_comm ((l : O) ^ c) (toB l O _ * toB l O _ : OB l O)]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialCocycleMemLPowLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.potentialCocycle_mem_lPow_lattice : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, ∀ c : ℕ, (l : K) ^ c • D.zeta y ∈ D.MM → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → (∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x) → ∃ x : ↥T.L.T, (l : O) ^ c • (actB (sQ l) T g b - b) = (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.BKGal.potential_cocycle_mem_lpow | exact GlobalTheory.BKGal.potential_cocycle_mem_lpow | (intros; apply GlobalTheory.BKGal.potential_cocycle_mem_lpow <;> assumption)
end
end
