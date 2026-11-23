module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
import Mathlib.Tactic.Polynomial.Basic
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThD
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThC

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh




open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

instance finDim (D : D7) : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _

structure GoodPl (χ : (AE D)ˣ →* Circle) (b₀ : HermE D ρ) (v : Pl D) : Prop where
  good : LFixW.IsGood D.host.F D.host.E v
  unr : ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1
  bint : ∀ i j, inclR (Fv D.host.F v) (b₀.1 i j) ∈ intLoc D.host.F D.host.E v

theorem eventually_unr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) :
    ∀ᶠ v in cofinite, ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1 := by
  classical
  let m : Pl D → (AE D)ˣ := fun v =>
    if h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 then h.choose else 1
  have hm : ∀ v, m v ∈ GlobalTheory.ThK.unitsAt D.host.E v := fun v => by
    simp only [m]
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_mem _
  filter_upwards [GlobalTheory.ThK.ConeEulerChr.eventually_chr_eq_one (ν := χ) hχ.1 m (Eventually.of_forall hm)] with v hv u hu
  by_contra hne
  have h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 := ⟨u, hu, hne⟩
  have e : m v = h.choose := dif_pos h
  exact h.choose_spec.2 (e ▸ hv)

theorem eventually_goodPl {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (b₀ : HermE D ρ) :
    ∀ᶠ v in cofinite, GoodPl χ b₀ v := by
  filter_upwards [LFixW.eventually_good (F := D.host.F) (E := D.host.E), eventually_unr hχ,
    eventually_all.2 fun i => eventually_all.2 fun j =>
      GlobalTheory.AdelicU.SelfDual.eventually_mem_intLoc (F := D.host.F) (b₀.1 i j)] with v h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem adj_apply (x : Mx D ρ p) (i : Fin p) (j : Fin ρ) : adj x i j = cA D (x j i) := rfl

theorem cv_cA (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (cA D), map_add (cv D v), map_add (cv D v), hx, hy, map_add (sigR (Fv D.host.F v) D.sp.cm.sig)]

theorem one_cn {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  rw [← block_matrix_one (R := R), block_matrix_apply_top_right, Matrix.zero_apply]

theorem unip_one {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v)
    (hker : ∀ y : AF D.host.F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers D.host.F) → ψ y = 1)
    {g : G D p} (hg : g ∈ KOff D p S) {b : Mx D p p} (hb : mat g = blk4 1 b 0 1) {y : Mx D ρ p} (hy : IntOff S y) :
    ψ (halfTr (b * pr b₀ y y).trace) = 1 := by
  have hbe : ∀ i j, b i j = mat g (Fin.castAdd p i) (Fin.natAdd p j) := fun i j => by rw [hb, block_matrix_apply_top_right]
  have hbInf : ∀ w i j, compInf D.host.F D.host.E w (b i j) = 0 := fun w i j => by
    rw [hbe, (kOff_entry hg _ _).1 w, one_cn]
  have hbS : ∀ v ∈ S, ∀ i j, cv D v (b i j) = 0 := fun v hv i j => by
    rw [hbe, (kOff_entry hg _ _).2.1 v hv, one_cn]
  have hbI : ∀ v ∉ S, ∀ i j, cv D v (b i j) ∈ intLoc D.host.F D.host.E v := fun v hv i j => by
    rw [hbe]; exact (kOff_entry hg _ _).2.2 v hv
  have hPI : ∀ v ∉ S, ∀ k i, cv D v (pr b₀ y y k i) ∈ intLoc D.host.F D.host.E v := by
    intro v hv k i

    simp only [pr, Matrix.mul_apply, map_sum, map_mul]
    refine sum_mem fun l _ => mul_mem ?_ (sum_mem fun m _ => mul_mem ?_ (hy v hv m i))
    · rw [adj_apply, cv_cA]; exact sigR_mem_intLoc _ (hy v hv l k)
    · rw [Matrix.map_apply]; exact (hS v hv).bint l m
  have hX : ∀ (R : Type) [CommRing R] (f : AE D →+* R), f (b * pr b₀ y y).trace =
      ∑ i, ∑ k, f (b i k) * f (pr b₀ y y k i) := fun R _ f => by

    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  have hXinf : ∀ w, compInf D.host.F D.host.E w (b * pr b₀ y y).trace = 0 := fun w => by
    rw [hX]; simp [hbInf]
  have hXS : ∀ v ∈ S, cv D v (b * pr b₀ y y).trace = 0 := fun v hv => by
    rw [hX]; simp [hbS v hv]
  have hXI : ∀ v ∉ S, cv D v (b * pr b₀ y y).trace ∈ intLoc D.host.F D.host.E v := fun v hv => by
    rw [hX]; exact sum_mem fun i _ => sum_mem fun k _ => mul_mem (hbI v hv i k) (hPI v hv k i)
  apply hker
  · refine funext fun w => ?_
    change evInf D.host.F w (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evInf_apply w (trA _), LFixW.trA_fst, hXinf, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, hXS v hv, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) ∈ _
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, AlgHom.commutes, one_div]
    exact mul_mem (hS v hv).good.half (LFixW.trace_mem (hS v hv).good (hXI v hv))

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.DetMemSubring

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh




open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p : ℕ}

theorem det_mem_subring {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ T) : M.det ∈ T := by
  let N : Matrix (Fin n) (Fin n) T := fun i j => ⟨M i j, h i j⟩
  have e : M = T.subtype.mapMatrix N := by ext i j; rfl
  rw [e, ← RingHom.map_det]
  exact (N.det).2

theorem evFin_eInf (v : Pl D) : evFin D.host.F v (GlobalTheory.ThK.ConeEuler.eInf D.host.F) = 0 := by
  rw [LFixW.evFin_apply, GlobalTheory.ThK.ConeEuler.eInf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd, LinearMap.inl_apply]
  rfl

theorem unitArch_eq_one (l : (AE D)ˣ) (hinf : ∀ w, compInf D.host.F D.host.E w (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1 := by
  apply Units.ext
  apply LIdemEx.ae_ext
  · intro w
    rw [GlobalTheory.IdeleCyl.compInf_unitArch, hinf, Units.val_one, map_one]
  · intro v
    change compFin D.host.F D.host.E v (GlobalTheory.ThK.ConeEuler.eInf D.host.F • (l : AE D) +
      (1 - GlobalTheory.ThK.ConeEuler.eInf D.host.F) • 1) = cv D v ((1 : (AE D)ˣ) : AE D)
    rw [map_add (f := _), GlobalTheory.ThK.compFin_smul, GlobalTheory.ThK.compFin_smul, evFin_eInf, map_sub, map_one, evFin_eInf, sub_zero,
      zero_smul, zero_add, one_smul, Units.val_one]

theorem unitAt_eq_one (l : (AE D)ˣ) (v : Pl D) (hat : cv D v (l : AE D) = 1) :
    GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1 := by
  apply Units.ext
  change GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • 1 = ((1 : (AE D)ˣ) : AE D)
  have h0 : compFin D.host.F D.host.E v ((l : AE D) - 1) = 0 := by
    rw [map_sub, map_one]; exact sub_eq_zero.2 hat
  have hk := GlobalTheory.InertLagUniq.liftV_one_smul_eq_zero (E := D.host.E) v _ h0
  have e : GlobalTheory.ThK.ConeEuler.eFin v • (l : AE D) + (1 - GlobalTheory.ThK.ConeEuler.eFin v) • (1 : AE D) =
      1 + GlobalTheory.ThK.ConeEuler.eFin v • ((l : AE D) - 1) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  rw [e, Units.val_one]
  change 1 + GlobalTheory.LatVac.liftV v 1 • ((l : AE D) - 1) = 1
  rw [hk, add_zero]

theorem chr_abs_one {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (l : (AE D)ˣ) (hA : GlobalTheory.ThK.ConeEuler.unitArch D.host.F D.host.E l = 1)
    (hAt : ∀ v ∈ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l = 1)
    (hmem : ∀ v ∉ S, GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l ∈ GlobalTheory.ThK.unitsAt D.host.E v) :
    χ l = 1 ∧ absE D.host.F D.host.E l = 1 := by
  have key := (GlobalTheory.ThK.ConeEulerChr.chr_abs_eq_finprod χ hχ.1 l 1).2
  have hfp : (∏ᶠ v : Pl D, (χ (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℂ) *
      ((absE D.host.F D.host.E (GlobalTheory.ThK.ConeEuler.unitAt D.host.E v l) : ℝ) : ℂ) ^ 1) = 1 := by
    rw [finprod_congr (g := fun _ => (1 : ℂ)) ?_, finprod_one]
    intro v
    by_cases hv : v ∈ S
    · rw [hAt v hv]; simp
    · have hm := hmem v hv
      rw [(hS v hv).unr _ hm, GlobalTheory.ThK.absE_of_mem_unitsAt hm]; simp
  rw [hfp, hA] at key
  simp only [map_one, Circle.coe_one, NNReal.coe_one, Complex.ofReal_one, mul_one, pow_one] at key
  have habs : absE D.host.F D.host.E l = 1 := by
    have hn := congrArg norm key
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, norm_one,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hn
    exact_mod_cast hn
  refine ⟨?_, habs⟩
  rw [habs, NNReal.coe_one, Complex.ofReal_one, mul_one] at key
  exact Circle.coe_eq_one.1 key

theorem levi_chr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v) (a : GL (Fin p) (AE D))
    (h1 : ∀ i j w, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h2 : ∀ i j, ∀ v ∈ S, cv D v (a.1 i j) = (1 : Matrix (Fin p) (Fin p) _) i j)
    (h3 : ∀ i j, ∀ v ∉ S, cv D v (a.1 i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((a⁻¹).1 i j) ∈ intLoc D.host.F D.host.E v) :
    χ (Matrix.GeneralLinearGroup.det a) = 1 ∧ absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
  have hv0 : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = (a : Matrix (Fin p) (Fin p) (AE D)).det :=
    Matrix.GeneralLinearGroup.val_det_apply a
  have hv1 : (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) =
      ((a⁻¹ : GL (Fin p) (AE D)) : Matrix (Fin p) (Fin p) (AE D)).det := by
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hinf : ∀ w, compInf D.host.F D.host.E w ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro w
    rw [hv0, RingHom.map_det]
    have e : (compInf D.host.F D.host.E w).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h1 i j w
    rw [e, Matrix.det_one]
  have hat : ∀ v ∈ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    rw [hv0, RingHom.map_det]
    have e : (cv D v).mapMatrix (a : Matrix (Fin p) (Fin p) (AE D)) = 1 := by
      ext i j; exact h2 i j v hv
    rw [e, Matrix.det_one]
  have hint : ∀ v ∉ S, cv D v ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (((Matrix.GeneralLinearGroup.det a)⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [hv0, hv1, RingHom.map_det, RingHom.map_det]
    exact ⟨det_mem_subring _ _ fun i j => (h3 i j v hv).1, det_mem_subring _ _ fun i j => (h3 i j v hv).2⟩
  refine chr_abs_one hχ hS _ (unitArch_eq_one _ hinf) (fun v hv => unitAt_eq_one _ v (hat v hv)) fun v hv => ?_
  refine GlobalTheory.ThK.mem_unitsAt.2 ⟨GlobalTheory.ThK.ConeEuler.unitAt_mem v _, ?_, ?_⟩
  · rw [GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).1
  · rw [← map_inv, GlobalTheory.ThK.ConeEuler.compFin_unitAt_self]; exact (hint v hv).2

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixTh

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open LFixTh

open Classical in


theorem fixTh : IdemEx → GenG → GenK → FixTh := by
  intro _ hG hK D ρ p m ψ hψ χ hχ θ _ b₀ hb₀
  obtain ⟨S₁, hS₁⟩ := hK D p
  obtain ⟨S₃, hS₃⟩ := LFixW.psi_kernel hψ
  obtain ⟨S₄, hS₄⟩ := LFixW.ft_supp b₀.1 hb₀ hψ
  have hgood := eventually_goodPl hχ b₀
  refine ⟨S₁ ∪ S₃ ∪ S₄ ∪ (Filter.eventually_cofinite.1 hgood).toFinset, fun S hS e he Ω hΩ hgoodΩ => ?_⟩
  have hSg : ∀ v ∉ S, GoodPl χ b₀ v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)))
  have hSI := hS₃ S (fun v hv => hS (by simp [hv]))
  have hS4 := hS₄ S (fun v hv => hS (by simp [hv])) e he p m.μ
  have : m.μ.IsAddHaarMeasure := m.hμ.1
  let A' : Set (G D p) := {x | Ω x = Ω 1}
  have hA'c : IsClosed A' := by
    have e : A' = ⋂ y, {x | Ω x y = Ω 1 y} := by
      ext x; simp only [A', Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq (hΩ.cont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hgen : ∀ g ∈ KOff D p S, (IsN g ∨ IsM g ∨ ∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D p S ∧ g = w * u * w⁻¹) →
      ∀ x ∈ A', g * x ∈ A' := by
    intro g hg hgt x hx
    simp only [A', Set.mem_ofPred_eq] at hx ⊢
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | ⟨w, u, hw, ⟨b, hb⟩, hu, rfl⟩
    · funext y
      rw [hΩ.unip g b hb x y, hx]
      by_cases hy : IntOff S y
      · rw [unip_one hSg hSI hg hb hy, one_mul]
      · rw [hgoodΩ y, if_neg hy, mul_zero]
    · have hbl := levi_blocks hg ha
      obtain ⟨h1, h2⟩ := levi_chr hχ hSg a (fun i j w => ((hbl i j).1 w).1) (fun i j v hv => ((hbl i j).2.1 v hv).1)
        (fun i j v hv => (hbl i j).2.2 v hv)
      funext y
      rw [hΩ.levi g a ha x y, hx, h1, h2, levi_good he hg ha _ hgoodΩ y]
      simp [npow]
    · let c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin p) (AE D)))) ((ρ : ℂ) / 2)
      have hΦ : ∀ y, Ω (w⁻¹ * x) y = ∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ := by
        intro y
        have e1 : w⁻¹ * x = w * ((w * w)⁻¹ * x) := by group
        rw [e1, hΩ.weyl w hw]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [hΩ.levi _ (-1) (mat_ww hw) x z, hx, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
      have hzero : ∀ y, ψ (halfTr (b * pr b₀ y y).trace) * Ω (w⁻¹ * x) y = Ω (w⁻¹ * x) y := by
        intro y
        by_cases hy : IntOff S y
        · rw [unip_one hSg hSI hu hb hy, one_mul]
        · rw [hΦ y, show (∫ z, (fun z => c * Ω 1 (-z)) z * ψ (trA (pr b₀ y z).trace) ∂m.μ) = 0 from
            hS4 this _ (good_neg hgoodΩ c) y hy, mul_zero]
      funext y
      have e2 : w * u * w⁻¹ * x = w * (u * (w⁻¹ * x)) := by group
      have e3 : Ω 1 y = Ω (w * (w⁻¹ * x)) y := by rw [mul_inv_cancel_left, hx]
      rw [e2, e3, hΩ.weyl w hw, hΩ.weyl w hw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      rw [hΩ.unip u b hb, hzero z]
  have hK' : (KOff D p S : Set (G D p)) ⊆ A' :=
    hS₁ S (fun v hv => hS (by simp [hv])) A' hA'c rfl hgen
  intro u hu h
  let A : Set (G D p) := {h | Ω (h * u) = Ω h}
  have hAc : IsClosed A := by
    have e : A = ⋂ y, {h | Ω (h * u) y = Ω h y} := by
      ext x; simp only [A, Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
    rw [e]
    exact isClosed_iInter fun y => isClosed_eq
      (hΩ.cont.comp ((continuous_mul_const u).prodMk continuous_const))
      (hΩ.cont.comp (continuous_id.prodMk continuous_const))
  have h1 : (1 : G D p) ∈ A := by
    show Ω (1 * u) = Ω 1
    rw [one_mul]; exact hK' hu
  have hA := hG D p A hAc h1 fun g hgt x hx => by
    show Ω (g * x * u) = Ω (g * x)
    have hx' : Ω (x * u) = Ω x := hx
    rcases hgt with ⟨b, hb⟩ | ⟨a, ha⟩ | hw
    · funext y; rw [mul_assoc, hΩ.unip g b hb, hΩ.unip g b hb, hx']
    · funext y; rw [mul_assoc, hΩ.levi g a ha, hΩ.levi g a ha, hx']
    · funext y; rw [mul_assoc, hΩ.weyl g hw, hΩ.weyl g hw, hx']
  have hh : h ∈ A := hA ▸ Set.mem_univ h
  exact hh

end PositivityTheory.Rg.Rsw.L

end
end
end
