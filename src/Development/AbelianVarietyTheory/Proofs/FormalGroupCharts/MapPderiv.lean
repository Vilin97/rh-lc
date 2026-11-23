module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AlgHomDualNumberExt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LawRightUnit
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibre
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAdicCompleteOfFgOfNatCastMem
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapMaximalIdealEqKerMapResidue
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MulFConstAndMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesMemMapCOfCoeffMem
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NonemptyTensorQuotientEquiv
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DetJacobianFormalMulNEqPowMulUnit

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace GlobalTheory.MulJacobian

variable {R : Type} [CommRing R] {d : ℕ}

theorem mulF_eq_mulN (G : FGLaw R d) (N : ℕ) : mulF G.F N = mulN G N := by
  induction N with
  | zero => rfl
  | succ n ih => rw [mulF, mulN, ih]

def invMat (G : FGLaw R d) : Matrix (Fin d) (Fin d) (PS R 1 d) :=
  Matrix.of fun j i => ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F j))

theorem const_invMat (G : FGLaw R d) (j i : Fin d) :
    constantCoeff (invMat G j i) = (1 : Matrix (Fin d) (Fin d) R) j i := by
  rw [invMat, Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev GlobalTheory.ChartTrans.axis_GP,
    ← GlobalTheory.FormalMulN.coeff_single_one, GlobalTheory.FormalMulN.lin_F_right, Matrix.one_apply]

theorem isUnit_det_of_const {σ : Type} (M : Matrix (Fin d) (Fin d) (MvPowerSeries σ R))
    (h : ∀ j i, constantCoeff (M j i) = (1 : Matrix (Fin d) (Fin d) R) j i) : IsUnit M.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff (σ := σ) (R := R)).mapMatrix M = 1 := by
    ext j i
    exact h j i
  rw [this, Matrix.det_one]
  exact isUnit_one

theorem dof_single (G : FGLaw R d) (c : R) (l : Fin d) (f : PS R 1 d) :
    Dof G.F (Pi.single l c) f = C c * ∑ j, pderiv ((0 : Fin 1), j) f * invMat G j l := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, invMat, Matrix.of_apply]
    ring
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, map_zero, zero_mul]
  · simp

theorem jac_mul_invMat (G : FGLaw R d) (N : ℕ) :
    (Matrix.of fun i j : Fin d => pderiv ((0 : Fin 1), j) (mulN G N i)) * invMat G =
      (N : PS R 1 d) • Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.FormalMulN.mulN_hom R d G N
  have hφ : GP (mulN G N) := h0
  ext1 i l
  have h := GlobalTheory.HomChain.dof_hom G G (mulN G N) h0 h1 (Pi.single l 1) (pt R d 0 i)
  have e1 : (dLin (mulN G N)).mulVec (Pi.single l 1) = Pi.single l (N : R) := by
    rw [h2, Matrix.smul_mulVec, Matrix.one_mulVec, ← Pi.single_smul, smul_eq_mul, mul_one]
  have e2 : ev (n := 1) ![mulN G N] (pt R d 0 i) = mulN G N i :=
    GlobalTheory.GaugeAdjoint.ev_pt (single_point_zero_constant hφ) 0 i
  have e3 : ∑ j, pderiv ((0 : Fin 1), j) (pt R (n := 1) d 0 i) * invMat G j l = invMat G i l := by
    rw [Finset.sum_eq_single i]
    · simp [pt]
    · intro j _ hj
      rw [pt, pderiv_X_of_ne (by simpa using hj.symm), zero_mul]
    · simp
  rw [e1, e2, dof_single, dof_single, e3, GlobalTheory.ChartTrans.ev_C_mul _ (single_point_zero_constant hφ), map_one, one_mul,
    map_natCast] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  exact h

theorem det_jac_mulF : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ),
    ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  intro R _ d G N
  have hφ : GP (mulN G N) := GlobalTheory.FormalMulN.const_mulN G N
  obtain ⟨a, ha⟩ := isUnit_det_of_const (invMat G) (const_invMat G)
  obtain ⟨b, hb⟩ := isUnit_det_of_const
    (Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l)) (fun i l => by
      rw [Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev (single_point_zero_constant hφ), const_invMat])
  have h := congrArg Matrix.det (jac_mul_invMat G N)
  rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, ← ha, ← hb] at h
  refine ⟨b * a⁻¹, ?_⟩
  rw [mulF_eq_mulN, Units.val_mul, ← mul_assoc, ← h, Units.mul_inv_cancel_right]

end GlobalTheory.MulJacobian
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.DetJacobianFormalMulNEqPowMulUnitStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ), ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv (R := R) ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  first | exact @GlobalTheory.MulJacobian.det_jac_mulF | exact GlobalTheory.MulJacobian.det_jac_mulF | (intros; apply GlobalTheory.MulJacobian.det_jac_mulF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibreStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalGroupLaw_chart_finiteHeight_specialFibre : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  first | exact @GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | exact GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | (intros; apply GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsReducedGenericFibreOfIsReduced

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_genericFibre_of_isReduced :
    ∀ (O C Q : Type) [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
      [CommRing Q] [Algebra O Q], IsReduced Q → IsReduced (C ⊗[O] Q) := by
  intro O C Q _ _ _ _ _ _ _ h
  letI : Algebra Q (C ⊗[O] Q) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Q (nonZeroDivisors O)) (C ⊗[O] Q) :=
    IsLocalization.tensorRight C (nonZeroDivisors O)
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid Q (nonZeroDivisors O))
    (C ⊗[O] Q) h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalTorsion

theorem map_pderiv {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) s f) = MvPowerSeries.pderiv (R := S) s (MvPowerSeries.map φ f) := by
  ext n
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv]

theorem map_bound {R S σ κ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : κ → MvPowerSeries σ R)
    (I : Ideal R) (M : ℕ)
    (h : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤
      Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) I) :
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ S)) ^ M ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map φ (f j)) ⊔
        Ideal.map (MvPowerSeries.C : S →+* MvPowerSeries σ S) (Ideal.map φ I) := by
  have h2 := Ideal.map_mono (f := MvPowerSeries.map φ) h
  rw [Ideal.map_pow, Ideal.map_span, Ideal.map_sup, Ideal.map_span, Ideal.map_map] at h2
  have e1 : (MvPowerSeries.map φ) '' Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R) =
      Set.range (MvPowerSeries.X : σ → MvPowerSeries σ S) := by
    rw [← Set.range_comp]
    congr 1
    funext s
    simp [MvPowerSeries.map_X]
  have e2 : (MvPowerSeries.map φ) '' Set.range f = Set.range fun j => MvPowerSeries.map φ (f j) := by
    rw [← Set.range_comp]
    rfl
  have e3 : (MvPowerSeries.map φ).comp (MvPowerSeries.C : R →+* MvPowerSeries σ R) =
      (MvPowerSeries.C : S →+* MvPowerSeries σ S).comp φ := by
    ext a
    simp [MvPowerSeries.map_C]
  rw [e1, e2, e3] at h2
  rw [Ideal.map_map]
  exact h2

theorem fhSt : ∀ (p : ℕ) [Fact p.Prime], FHSt p := by
  intro p _
  unfold FHSt
  intro T _ _ _ _ _ _ hp G _ _ D A hU d F x hx C _ _ _ v O _ _ hv _ _ iota hiota m
  unfold QF
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  have hN1 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
  have hNd : (p ^ m) ^ d ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp0)

  let e : Fin d ≃ Fin 1 × Fin d :=
    { toFun := fun j => (0, j), invFun := fun q => q.2, left_inv := fun _ => rfl,
      right_inv := fun q => Prod.ext (Subsingleton.elim _ _) rfl }
  let _ : Algebra T O := iota.toAlgebra
  have : IsDomain O := hv.hom_inj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : IsFractionRing O C := hv.isFractionRing

  have hc : ∀ j, MvPowerSeries.constantCoeff (mulF F.F (p ^ m) j) = 0 := fun j =>
    (GlobalTheory.FormalMul.mulF_const_and_map T O iota d F (p ^ m) j).1
  have hmap : ∀ j, mulF (F.mapF iota) (p ^ m) j = MvPowerSeries.map iota (mulF F.F (p ^ m) j) :=
    fun j => (GlobalTheory.FormalMul.mulF_const_and_map T O iota d F (p ^ m) j).2

  obtain ⟨M, hM⟩ := GlobalTheory.T.formalGroupLaw_chart_finiteHeight_specialFibre T G D A hU d F x hx (p ^ m) hN1
  obtain ⟨hFree, hFin⟩ := GlobalTheory.FiniteColength.free_finite_quotient T inferInstance (Fin 1 × Fin d) d e
    (mulF F.F (p ^ m)) hc ⟨M, hM⟩
  have hMT := GlobalTheory.span_X_pow_le_sup_of_residue T (Fin 1 × Fin d) (Fin d) (mulF F.F (p ^ m)) M hM

  have hFGT : (maximalIdeal T).FG := IsNoetherian.noetherian _
  have hJfg : ((maximalIdeal T).map iota).FG := hFGT.map iota
  have hJle : (maximalIdeal T).map iota ≤ maximalIdeal O :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit iota a ha
  have hJne : (maximalIdeal T).map iota ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 (h ▸ hJle))
  have hpT : (p : T) ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).2 hp
  have hpJ : (p : O) ∈ (maximalIdeal T).map iota := by
    simpa using Ideal.mem_map_of_mem iota hpT
  have hJc : IsAdicComplete ((maximalIdeal T).map iota) O :=
    GlobalTheory.isAdicComplete_of_fg_of_natCast_mem C v O hv p hp0 inferInstance _ hJfg hJne hpJ

  obtain ⟨eqv⟩ := GlobalTheory.QuotientBaseChange.nonempty_tensor_quotient_equiv T O (maximalIdeal T) hFGT hJc
    (Fin 1 × Fin d) (Fin d) (mulF F.F (p ^ m)) M hMT hFree hFin
  have hspan : (Set.range fun j => MvPowerSeries.map (algebraMap T O) (mulF F.F (p ^ m) j)) =
      Set.range (mulF (F.mapF iota) (p ^ m)) := by
    congr 1
    funext j
    exact (hmap j).symm
  rw [hspan] at eqv
  have hFO : Module.Free O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    Module.Free.of_equiv eqv.toLinearEquiv
  have hFinO : Module.Finite O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    Module.Finite.equiv eqv.toLinearEquiv

  have hMO := map_bound iota (mulF F.F (p ^ m)) (maximalIdeal T) M hMT
  have hfun : (fun j => MvPowerSeries.map iota (mulF F.F (p ^ m) j)) = mulF (F.mapF iota) (p ^ m) :=
    funext fun j => (hmap j).symm
  rw [hfun] at hMO
  obtain ⟨U, hU8⟩ := GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit T d F (p ^ m)
  have h2 : Matrix.of (fun i j : Fin d => MvPowerSeries.pderiv (R := O) (e j) (mulF (F.mapF iota) (p ^ m) i)) =
      (MvPowerSeries.map iota).mapMatrix
        (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv (R := T) ((0 : Fin 1), j) (mulF F.F (p ^ m) i)) := by
    ext i j
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [map_pderiv, hmap]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv (R := O) (e j) (mulF (F.mapF iota) (p ^ m) i)) =
      (((p ^ m) ^ d : ℕ) : MvPowerSeries (Fin 1 × Fin d) O) *
        (Units.map (MvPowerSeries.map iota).toMonoidHom U : (MvPowerSeries (Fin 1 × Fin d) O)ˣ) := by
    rw [h2, ← RingHom.map_det, hU8, map_mul, map_pow, map_natCast]
    simp only [Nat.cast_pow]
    rfl
  have hdn := GlobalTheory.NoTangent.algHom_dualNumber_ext C v O hv p hp0 inferInstance _ hJfg hJne hpJ
    (Fin 1 × Fin d) d e (mulF (F.mapF iota) (p ^ m)) M ((p ^ m) ^ d) _ hNd hMO hdet

  obtain ⟨-, hsep, -⟩ := GlobalTheory.finEtale_main C O (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) v hv hdn
  have hred : IsReduced (MvPowerSeries (Fin 1 × Fin d) O ⧸
      Ideal.span (Set.range (mulF (F.mapF iota) (p ^ m)))) :=
    ⟨fun q hq => hsep q fun φ => (hq.map φ).eq_zero⟩
  exact ⟨hFO, hFinO, GlobalTheory.isReduced_genericFibre_of_isReduced O C _ hred, hsep⟩

end GlobalTheory.FormalTorsion
end
end
