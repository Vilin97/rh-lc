module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersCharOnNormOneIdelesMulUnramifiedClassValueStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanion

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatCoCompan


open Formalism.L2.GlobalTheoryTheory.Comp in
theorem latCo_eq_latAd_compan : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  intro D i hi co hco a x Lb hfin hspan
  have horth : IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) := by
    intro u v
    have h := hform_mulVec_rect (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (co.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) u v
    rw [Matrix.mul_one] at h
    have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) co.1 * co.1 = (gramN D i hi) := hco
    rw [hc] at h
    have e1 : hform (D.sp.cm.sig : D.host.E →+* D.host.E) 1 (co.1 *ᵥ u) (co.1 *ᵥ v) =
        ∑ b, (D.sp.cm.sig : D.host.E →+* D.host.E) ((co.1 *ᵥ u) b) * (co.1 *ᵥ v) b := by
      simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [e1] at h
    exact h
  have hJ : ∀ M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E), IsLat M → IsLat (dl D.sp.cm.sig (gramN D i hi) M) :=
    fun M hM => GlobalTheory.OrthDual.isLat_dl D.sp.cm.sig (gramN D i hi) (toLE co) horth M hM
  have hLb : IsLat Lb := ⟨hfin, hspan⟩
  have hx : x.1 ∈ UPts D.sp.cm.sig (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := x.2
  have hC : IsLat (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero]; exact hLb
    · rw [GlobalTheory.SDCompan.compan_eq]; exact isLat_sup hLb (isLat_smul (hJ _ hLb) ha)
  refine ⟨?_, hC.1, hC.2⟩
  have hG : compan (sp := D.sp) (gramN D i hi) a (latAd x.1 Lb) = latAd x.1 (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero, GlobalTheory.SDCompan.compan_zero]
    · rw [GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.latAd_eq, GlobalTheory.SDCompan.latAd_eq]
      symm
      rw [glob_sup hLb (isLat_smul (hJ _ hLb) ha), glob_smul (hJ _ hLb) ha,
        glob_dl D.sp.cm.sig (gramN D i hi) hJ hLb x.1 hx]
  unfold latCo
  rw [hG, latAd_rat]

end GlobalTheory.LatCoCompan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | exact GlobalTheory.LatCoCompan.latCo_eq_latAd_compan | (intros; apply GlobalTheory.LatCoCompan.latCo_eq_latAd_compan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCoordsConjUnitaryAndCarriesCompanion

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCarry

theorem mem_hatL_latAd_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ Formalism.L2.Herm.hatL (F := F) (latAd x Lb) ↔
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x u
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  exact hrec

theorem carries_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (C y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (M : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤) :
    Formalism.L2.Herm.Carries (F := F) (C * y * C⁻¹) (latAd C M) (latAd (C * y) M) := by
  intro x
  rw [mem_hatL_latAd_iff (C * y) M hfin hspan, mem_hatL_latAd_iff C M hfin hspan, Matrix.mulVec_mulVec, ← Units.val_mul]
  have e : C⁻¹ * (C * y * C⁻¹)⁻¹ = (C * y)⁻¹ := by group
  rw [e]

theorem cT_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {N : ℕ}
    (σ : E →ₐ[F] E) (M : Matrix (Fin N) (Fin N) E) :
    cT (sigR σ R) (M.map (inclE (F := F) R)) = (cT (σ : E →+* E) M).map (inclE (F := F) R) := by
  ext a b
  simp [cT, sigR, inclE]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem conj_mem_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ratA F co * y * (ratA F co)⁻¹ ∈ UPts σ (1 : Matrix (Fin N) (Fin N) E) (FiniteAdeleRing (𝓞 F) F) := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] R) := ((ratA F co : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCm
  set Ci : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (((ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCi
  set Y : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hY
  have hCm' : Cm = co.1.map (inclE (F := F) R) := rfl
  have hJ : cT s Cm * Cm = J.map (inclE (F := F) R) := by
    rw [hCm', cT_map_incl, ← Matrix.map_mul, hco]
  have hy' : cT s Y * J.map (inclE (F := F) R) * Y = J.map (inclE (F := F) R) := hy
  have hCC : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  show cT s ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) *
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) * ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R)
  rw [h1, Units.val_mul, Units.val_mul, ← hCm, ← hCi, ← hY, Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Ci * (cT s Y * cT s Cm) * (Cm * Y * Ci)
      = cT s Ci * (cT s Y * (cT s Cm * Cm) * Y) * Ci := by simp only [Matrix.mul_assoc]
    _ = cT s Ci * (cT s Cm * Cm) * Ci := by rw [hJ, hy']
    _ = cT s (Cm * Ci) * (Cm * Ci) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hCC, cT_one, Matrix.one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem exists_stdUnitaryPoint_det_eq_unitaryPoint_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), d ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det d = Matrix.GeneralLinearGroup.det y := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set u := Matrix.GeneralLinearGroup.det y with hu
  refine ⟨Units.map (Matrix.scalar (Fin 1) : E ⊗[F] R →+* Matrix (Fin 1) (Fin 1) (E ⊗[F] R)).toMonoidHom u, ?_, ?_⟩
  ·
    have hy' : cT s (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) * J.map (inclE (F := F) R) * (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
        J.map (inclE (F := F) R) := hy
    have hdet := congrArg Matrix.det hy'
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hcT : ∀ M : Matrix (Fin N) (Fin N) (E ⊗[F] R), (cT s M).det = s M.det := by
      intro M
      unfold cT
      rw [Matrix.det_transpose, RingHom.map_det]
      rfl
    have hJu : IsUnit (J.map (inclE (F := F) R)).det := by
      show IsUnit ((inclE (F := F) R).mapMatrix J).det
      rw [← RingHom.map_det]
      refine IsUnit.map _ ?_
      have hco' : IsUnit (co : Matrix (Fin N) (Fin N) E).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
      rw [← hco, Matrix.det_mul]
      refine IsUnit.mul ?_ hco'
      unfold cT
      rw [Matrix.det_transpose]
      show IsUnit (((σ : E →+* E)).mapMatrix (co : Matrix (Fin N) (Fin N) E)).det
      rw [← RingHom.map_det]
      exact hco'.map _
    rw [hcT] at hdet
    have hn : s (u : E ⊗[F] R) * (u : E ⊗[F] R) = 1 := by
      have h2 : (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det = 1 * (J.map (inclE (F := F) R)).det := by
        calc (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det
            = s (u : E ⊗[F] R) * (J.map (inclE (F := F) R)).det * (u : E ⊗[F] R) := by ring
          _ = (J.map (inclE (F := F) R)).det := by rw [hu, Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
          _ = 1 * (J.map (inclE (F := F) R)).det := (one_mul _).symm
      exact hJu.mul_right_cancel h2
    have h1 : (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    show cT s _ * (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) * _ = (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R)
    rw [h1, Matrix.mul_one]
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, hn]
  · ext
    simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_one]

theorem det_conj {R : Type} [CommRing R] {N : ℕ} (C y : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (C * y * C⁻¹) = Matrix.GeneralLinearGroup.det y := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.TwV


open GlobalTheory.ConjCarry in
theorem conj_crd_unitary_carries : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β y
  have hco := hPins.crd_orth i hi
  have hLbf := ((St i hi).K β).lev.Lb_fin
  have hLbs := ((St i hi).K β).lev.Lb_span
  obtain ⟨e1, hCf, hCs⟩ := GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a 1 _ hLbf hLbs
  have e2 := (GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a y _ hLbf hLbs).1
  have e1' : latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb =
      latAd (ratA D.host.F (A.crd i hi)) (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb) := by
    have := e1
    simp only [OneMemClass.coe_one, mul_one] at this
    exact this
  refine ⟨conj_mem_std (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2, ?_, ?_⟩
  · rw [e1', e2]
    exact carries_conj _ _ _ hCf hCs
  · obtain ⟨d, hd, hdd⟩ := exists_stdUnitaryPoint_det_eq_unitaryPoint_det (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2
    refine ⟨⟨d, hd⟩, hdd, ?_⟩
    exact hdd.trans (GlobalTheory.ConjCarry.det_conj (ratA D.host.F (A.crd i hi)) y.1).symm

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCoordsConjUnitaryAndCarriesCompanionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  first | exact @GlobalTheory.TwV.conj_crd_unitary_carries | exact GlobalTheory.TwV.conj_crd_unitary_carries | (intros; apply GlobalTheory.TwV.conj_crd_unitary_carries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDet

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.DetIdChi

open Matrix

theorem heq_transport (D : D7) {n N : ℕ} (h : n = N) (K : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (K' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (hK : HEq K K') :
    (IsSDLat D.host.E n K → IsSDLat D.host.E N K') ∧ TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) K = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) K' := by
  subst h
  cases eq_of_heq hK
  exact ⟨id, rfl⟩

def coGL {E : Type} [Field E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : GL (Fin N) E :=
  ⟨LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)), LinearMap.toMatrix' ((f.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩

theorem toLE_coGL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : toLE (coGL f) = f := by
  refine LinearEquiv.ext fun x => ?_
  rw [toLE_apply]
  show LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)) *ᵥ x = f x
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem inv_mul_mem_UJ {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (G : Matrix (Fin N) (Fin N) E)
    (crd co : GL (Fin N) E) (h1 : cT σ crd.1 * crd.1 = G) (h2 : star co.1 * co.1 = G) : crd⁻¹ * co ∈ UJ σ G := by
  show cT σ ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * G * ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = G
  rw [← Emat.star_eq_cT σ hσ] at h1 ⊢
  rw [Units.val_mul, star_mul, ← h1]
  have e : star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have e' : (crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := Units.mul_inv crd
  calc star (co : Matrix (Fin N) (Fin N) E) * star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (star (crd : Matrix (Fin N) (Fin N) E) * crd) *
        (((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * co)
      = star (co : Matrix (Fin N) (Fin N) E) * (star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E)) *
        ((crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) * co := by
          simp only [Matrix.mul_assoc]
    _ = star (co : Matrix (Fin N) (Fin N) E) * co := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
    _ = star (crd : Matrix (Fin N) (Fin N) E) * crd := by rw [h2, h1]

end GlobalTheory.TwV.Xc.DetIdChi

open GlobalTheory.TwV.Xc.DetIdChi in

theorem GlobalTheory.TwV.Xc.chi_detId_kerN_eq : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl j hj
  have hσ : ∀ x : D.host.E, (sigD D : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  set G := gramN D j hj with hG
  set crd := J.A.crd j hj with hcrd
  have hco := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (sigD D : D.host.E →+* D.host.E) hσ (D.R.N j) (D.R.N j) rfl G crd
    (J.pins.crd_orth j hj)).1
  set co : GL (Fin (D.R.N j)) D.host.E := coGL (stdCo (sigD D : D.host.E →+* D.host.E) G) with hcoDef
  have hco2 : star co.1 * co.1 = G := Emat.gram_of_orth _ hσ G _ hco
  set γ₀ := crd⁻¹ * co with hγ₀
  have hγ : γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) G := inv_mul_mem_UJ _ hσ G crd co (J.pins.crd_orth j hj) hco2
  have hr : GlobalTheory.TwU.ratA D.host.F γ₀ ∈ UPts (sigD D) G (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ₀, hγ, rfl⟩
  have hch := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hDict hSpl
  refine ⟨chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)), ?_⟩

  have key : ∀ (β : (J.St j hj).Ch) (x : UA D j hj), IsSDLat D.host.E _ (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb) →
      t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb)) =
        chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)) * chiI J (Matrix.GeneralLinearGroup.det x.1) := by
    intro β x hsd
    let y : UA D j hj := ⟨GlobalTheory.TwU.ratA D.host.F γ₀ * x.1, mul_mem hr x.2⟩
    have hlat : latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb = GlobalTheory.TwU.latCo D.sp G crd J.a y.1 ((J.St j hj).K β).lev.Lb := by
      rw [← GlobalTheory.TwU.latCo_eq_latK G co (toLE_coGL _), show co = crd * γ₀ by rw [hγ₀, mul_inv_cancel_left]]
      exact GlobalTheory.TwU.latCo_mul G crd γ₀ hγ J.a x.1 _
    obtain ⟨hg, hcar, d, hdd, hdet⟩ := GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion J.A J.dtU J.a J.pins J.tie j hj β y
    rw [J.base j hj β] at hcar
    have hstd : IsSDLat D.host.E (D.R.N j) (StandardLatticesGL3.stdL D (D.R.N j)) := by
      have := ((t.O u μ).L0 j).2
      rwa [Formalism.L2.Ker.initial_lattice_eq_standard] at this
    rw [hlat] at hsd ⊢
    have hrel := J.rel (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩ _ hg hcar d hdet
    have hid := t.idl_ok.2.2.2.2 (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩
    rw [hrel] at hid
    have hx1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj x
    have hy1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj y
    have hr1 : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) ∈ U1 (sigD D) := by
      have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) =
          Matrix.GeneralLinearGroup.det y.1 * (Matrix.GeneralLinearGroup.det x.1)⁻¹ := by
        show _ = Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀ * x.1) * _
        rw [MonoidHom.map_mul Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) x.1, mul_inv_cancel_right]
      rw [e]
      exact mul_mem hy1 (inv_mem hx1)
    rw [← hch.1 _ hr1 _ hx1, show Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) * Matrix.GeneralLinearGroup.det x.1 =
      Matrix.GeneralLinearGroup.det d.1 by rw [hdd]; exact (map_mul _ _ _).symm, hch.2.2.1 d]
    show t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N j)) (⟨_, hsd⟩ : SDLat D.host.E (D.R.N j)).1) = _
    rw [← hid, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl
  intro La hLa hsd
  obtain ⟨⟨hr', -⟩, -, hheq, hdt⟩ := hDict j hj La hLa
  obtain ⟨h1, h2⟩ := heq_transport D hr' _ _ hheq
  rw [h2, hdt]
  exact key _ _ (h1 hsd)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDetStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  first | exact @GlobalTheory.TwV.Xc.chi_detId_kerN_eq | exact GlobalTheory.TwV.Xc.chi_detId_kerN_eq | (intros; apply GlobalTheory.TwV.Xc.chi_detId_kerN_eq <;> assumption)
end
end
