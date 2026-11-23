module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FinitePartMemIntegralAdeles

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

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

section Gen

theorem tmul_den {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] (x : A) {c : F}
    (hc : c ≠ 0) (b : E) : (x * algebraMap F A c⁻¹) ⊗ₜ[F] (c • b) = x ⊗ₜ[F] b := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_left_comm, ← map_mul,
    mul_inv_cancel₀ hc, map_one, mul_one]

theorem map_smul_basis {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (r : R) (k : ι) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (r • Algebra.TensorProduct.basis R b k) = φ r ⊗ₜ[F] b k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Gen

variable {D : D7}

abbrev bA (D : D7) := Algebra.TensorProduct.basis (AF D.host.F) (bE D.host.F D.host.E)

theorem crd_cv (v : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (bV (E := D.host.E) v).repr (cv D v z) k = evFin D.host.F v ((bA D).repr z k) :=
  LIdemEx.repr_map' (evFin D.host.F v) (bE D.host.F D.host.E) z k

theorem finPart_plc_mem (v : Pl D) {t : Fv D.host.F v ⊗[D.host.F] D.host.E} (ht : t ∈ intLoc D.host.F D.host.E v) :
    finPart D (plc D.host.E v t) ∈ intAE D := by
  refine intLoc_induction (p := fun t => finPart D (plc D.host.E v t) ∈ intAE D) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [LinearMap.map_add (f := _), RingHom.map_add (f := _)]; exact add_mem hy hz)
    (fun y hy => by rw [LinearMap.map_neg, RingHom.map_neg]; exact neg_mem hy) ht
  rw [plc_tmul]
  refine AddSubgroup.subset_closure ⟨(iV v a).2, fun w => ?_, x, rfl⟩
  by_cases h : w = v
  · subst h
    show (iV w a).2 w ∈ _
    rw [show (iV w a).2 w = a from GlobalTheory.CompanionTheory.PsiCondLoc.single_self w a]
    exact ha
  · show (iV v a).2 w ∈ _
    rw [show (iV v a).2 w = 0 from GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v a h]
    exact zero_mem _

theorem finPart_mem_of_good {z : AE D} (hb : ∀ v, ¬ IsGood D.host.F D.host.E v → cv D v z = 0)
    (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by

  rw [← (bA D).sum_repr z, map_sum]
  refine sum_mem fun k _ => ?_
  have hN : (den (bE D.host.F D.host.E k) : D.host.F) ≠ 0 := by exact_mod_cast den_ne (bE D.host.F D.host.E k)
  let o : 𝓞 D.host.E := ⟨(den (bE D.host.F D.host.E k) : D.host.E) * bE D.host.F D.host.E k, den_int _⟩
  have ho : (o : D.host.E) = (den (bE D.host.F D.host.E k) : D.host.F) • bE D.host.F D.host.E k := by
    rw [Algebra.smul_def, map_intCast]
    rfl
  have e1 : finPart D ((bA D).repr z k • (bA D) k) =
      sndA D.host.F ((bA D).repr z k) ⊗ₜ[D.host.F] bE D.host.F D.host.E k :=
    map_smul_basis (sndA D.host.F) (bE D.host.F D.host.E) _ k
  rw [e1]
  refine AddSubgroup.subset_closure ⟨sndA D.host.F ((bA D).repr z k) *
    algebraMap D.host.F (Af D.host.F) ((den (bE D.host.F D.host.E k) : D.host.F))⁻¹, fun v => ?_, o,
    by rw [ho]; exact (tmul_den _ hN _).symm⟩
  show evalV D.host.F v (sndA D.host.F ((bA D).repr z k) * algebraMap D.host.F (Af D.host.F) _) ∈ _
  rw [map_mul, AlgHom.commutes]
  have hc : evalV D.host.F v (sndA D.host.F ((bA D).repr z k)) = (bV (E := D.host.E) v).repr (cv D v z) k :=
    (crd_cv v z k).symm
  rw [hc]
  by_cases hv : IsGood D.host.F D.host.E v
  · exact mul_mem ((mem_intLoc_iff hv _).1 (hz v) k) (hv.deninv k)
  · rw [hb v hv, map_zero, Finsupp.zero_apply, zero_mul]
    exact zero_mem _

open Classical in
theorem cv_sub_plc (z : AE D) (B : Finset (Pl D)) (z' : AE D) (hz' : z' = z - ∑ v ∈ B, plc D.host.E v (cv D v z))
    (w : Pl D) : cv D w z' = if w ∈ B then 0 else cv D w z := by

  rw [hz', RingHom.map_sub, map_sum]
  by_cases hw : w ∈ B
  · rw [if_pos hw, Finset.sum_eq_single w (fun v _ hv => compFin_plc_ne (Ne.symm hv) _) (fun h => absurd hw h),
      compFin_plc_self, sub_self]
  · rw [if_neg hw, Finset.sum_eq_zero (fun v hv => compFin_plc_ne (fun h => hw (by rw [h]; exact hv)) _), sub_zero]

open Classical in
theorem finite_part_mem_integral_adeles (z z' : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v)
    (hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite) (B : Finset (Pl D)) (hB : B = hfin.toFinset)
    (hcv : ∀ w, cv D w z' = if w ∈ B then 0 else cv D w z) : finPart D z' ∈ intAE D := by
  refine finPart_mem_of_good (fun v hv => ?_) (fun v => ?_)
  · rw [hcv, if_pos (by rw [hB]; exact (Set.Finite.mem_toFinset hfin).2 hv)]
  · rw [hcv]
    split_ifs
    · exact zero_mem _
    · exact hz v

theorem finPart_mem (z : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  have hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite :=
    Filter.eventually_cofinite.1 (eventually_good (F := D.host.F) (E := D.host.E))
  have h1 := finite_part_mem_integral_adeles z _ hz hfin _ rfl (cv_sub_plc z hfin.toFinset _ rfl)
  have e : z = (z - ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z)) + ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z) :=
    (sub_add_cancel _ _).symm

  rw [e, RingHom.map_add (f := _), map_sum]
  exact add_mem h1 (sum_mem fun v _ => finPart_plc_mem v (hz v))

theorem infPart_eq_one {z : AE D} (h : ∀ w, compInf D.host.F D.host.E w z = 1) : infPart D z = 1 := by
  let bI := Algebra.TensorProduct.basis (Ainf D.host.F) (bE D.host.F D.host.E)
  apply bI.repr.injective
  refine Finsupp.ext fun k => ?_
  have h1 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) z k
  have h2 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) (1 : AE D) k
  have e1 : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
  have e2 : (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) =
      Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 : AE D) := (map_one _).symm
  rw [e1, e2, h1, h2]
  funext w
  have g1 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) z k
  have g2 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) (1 : AE D) k
  have hz : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) 1 := by
    rw [map_one]; exact h w
  rw [hz] at g1
  exact g1.symm.trans g2

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.NatCastMulGen

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

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

variable {D : D7}

theorem norm_mem {v : Pl D} (hv : IsGood D.host.F D.host.E v) {x : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hx : x ∈ intLoc D.host.F D.host.E v) :
    Algebra.norm (Fv D.host.F v) x ∈ v.adicCompletionIntegers D.host.F := by
  classical
  rw [Algebra.norm_eq_matrix_det (bV (E := D.host.E) v), Matrix.det_apply]
  have hM : ∀ i j, Algebra.leftMulMatrix (bV (E := D.host.E) v) x i j ∈ v.adicCompletionIntegers D.host.F := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb : bV (E := D.host.E) v j ∈ intLoc D.host.F D.host.E v := by
      rw [bV_apply]; exact one_tmul_b_mem hv j
    exact (mem_intLoc_iff hv _).1 (mul_mem hx hb) i
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

theorem absEv_eq_one {v : Pl D} (hv : IsGood D.host.F D.host.E v) (x : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (h1 : (x : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v)
    (h2 : ((x⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v) :
    absEv D.host.F D.host.E v x = 1 := by
  have k : ∀ y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v → absEv D.host.F D.host.E v y ≤ 1 := fun y hy => by
    rw [absEv_apply]
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (norm_mem hv hy)
  have a1 := k x h1
  have a2 := k _ h2
  have hm : absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ := hm.symm
    _ ≤ absEv D.host.F D.host.E v x * 1 := mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = absEv D.host.F D.host.E v x := mul_one _

def cN (D : D7) (N : ℕ) : AE D := algebraMap D.host.F (AF D.host.F) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cv_cN (v : Pl D) (N : ℕ) :
    cv D v (cN D N) = algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show evFin D.host.F v (algebraMap D.host.F (AF D.host.F) _) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [AlgHom.commutes]

theorem natCast_mul_gen {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {N : ℕ}
    (hN : (N : F) ≠ 0) : (N : A ⊗[F] E) * (algebraMap F A ((N : F)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [(map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := A) (B := E)) N).symm]
  show ((N : A) ⊗ₜ[F] (1 : E)) * _ = 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_natCast (algebraMap F A) N, ← map_mul,
    mul_inv_cancel₀ hN, map_one]
  rfl

theorem natCast_mul_cN {N : ℕ} (hN : 0 < N) : (N : AE D) * cN D N = 1 :=
  natCast_mul_gen (by exact_mod_cast hN.ne')

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv

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

namespace PositivityTheory.Rg.Rsw.L.LFixW



open U2 in
theorem unit_triv (D : D7) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) : ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
    ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) →
    χ u = 1 ∧ absA D u = 1 := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hbad : {v : Pl D | ¬ (IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F)}.Finite :=
    Filter.eventually_cofinite.1 ((eventually_good (F := D.host.F) (E := D.host.E)).and
      (eventually_int (F := D.host.F) ((N : D.host.F)⁻¹)))
  refine ⟨hbad.toFinset, fun S hS u hinf hSv hoff => ?_⟩
  have hgood : ∀ v ∉ S, IsGood D.host.F D.host.E v ∧
      algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    by_contra h
    exact hv (hS ((Set.Finite.mem_toFinset hbad).2 h))
  have hinv : ∀ v ∈ S, cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    intro v hv
    have := congrArg (cv D v) u.inv_mul
    rw [RingHom.map_mul, RingHom.map_one, hSv v hv, mul_one] at this
    exact this
  have hint : ∀ z : AE D, (∀ v ∈ S, cv D v z ∈ intLoc D.host.F D.host.E v) →
      (∀ v ∉ S, cv D v z ∈ intLoc D.host.F D.host.E v) → finPart D z ∈ intAE D := by
    intro z h1 h2
    refine finPart_mem z fun v => ?_
    by_cases hv : v ∈ S
    · exact h1 v hv
    · exact h2 v hv
  have hfu : FinUnit u := ⟨infPart_eq_one hinf,
    hint _ (fun v hv => by rw [hSv v hv]; exact one_mem _) (fun v hv => (hoff v hv).1),
    hint _ (fun v hv => by rw [hinv v hv]; exact one_mem _) (fun v hv => (hoff v hv).2)⟩
  have hy1 : ∀ v ∈ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, hSv v hv, RingHom.map_one, sub_self, mul_zero]
    exact zero_mem _
  have hy2 : ∀ v ∉ S, cv D v (cN D N * ((u : AE D) - 1)) ∈ intLoc D.host.F D.host.E v := by
    intro v hv
    rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    have ha : cv D v (cN D N) ∈ intLoc D.host.F D.host.E v := by
      rw [cv_cN]
      exact tmul_one_mem (E := D.host.E) (hgood v hv).2
    have hb : cv D v (u : AE D) - 1 ∈ intLoc D.host.F D.host.E v :=
      (intLoc D.host.F D.host.E v).sub_mem (hoff v hv).1 (intLoc D.host.F D.host.E v).one_mem
    exact (intLoc D.host.F D.host.E v).mul_mem ha hb
  have hy3 : finPart D (u : AE D) - 1 = N • finPart D (cN D N * ((u : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← map_natCast (finPart D) N, ← RingHom.map_mul, ← mul_assoc, natCast_mul_cN hN, one_mul,
      RingHom.map_sub, RingHom.map_one]
  refine ⟨hker u hfu ⟨_, hint _ hy1 hy2, hy3⟩, ?_⟩
  show absE D.host.F D.host.E u = 1
  rw [absE_apply]
  have h1 : ∀ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w u) = 1 := fun w => by
    rw [show unitInf D.host.F D.host.E w u = 1 from Units.ext (hinf w), map_one]
  have h2 : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v u) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · rw [show unitFin D.host.F D.host.E v u = 1 from Units.ext (hSv v hv), map_one]
    · exact absEv_eq_one (hgood v hv).1 _ (hoff v hv).1 (hoff v hv).2
  rw [Finset.prod_eq_one fun w _ => h1 w, finprod_congr h2, finprod_one, one_mul]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end
end
