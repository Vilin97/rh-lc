module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsomet

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory

theorem trEll_latticeConj_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n n' P J J' L L' v j hj
  obtain ⟨a, ha, -, hja⟩ := hj
  have iso : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J x φ → IsIsom P (Fv F v) J' x (φ.trans a) := by
    intro x φ h y y'
    have e := ha (φ y) (φ y')
    simp only [GlobalTheory.AdelicU.hLin, hR] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e]
    exact h y y'
  have iso' : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J' x φ → IsIsom P (Fv F v) J x (φ.trans a.symm) := by
    intro x φ h y y'
    have e := ha (a.symm (φ y)) (a.symm (φ y'))
    simp only [GlobalTheory.AdelicU.hLin, hR, LinearEquiv.apply_symm_apply] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← e]
    exact h y y'
  have tor : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
      (h : IsIsom P (Fv F v) J x φ) (t : Tor P (Fv F v)), torEmb (iso x φ h) t = j (torEmb h t) := by
    intro x φ h t
    apply GlobalTheory.AdelicU.matHom_injective (Fv F v) σ J'
    apply Units.ext
    have key : ∀ w, (GlobalTheory.AdelicU.matHom _ σ J' (torEmb (iso x φ h) t)).1 *ᵥ w =
        (GlobalTheory.AdelicU.matHom _ σ J' (j (torEmb h t))).1 *ᵥ w := by
      intro w
      obtain ⟨y, rfl⟩ := (φ.trans a).surjective w
      rw [LinearEquiv.trans_apply, hja]
      change mulMat (φ.trans a) (torUnit t).1 *ᵥ (φ.trans a) y = a (mulMat φ (torUnit t).1 *ᵥ φ y)
      rw [mulMat_mulVec, mulMat_mulVec]
      rfl
    exact Matrix.ext_of_mulVec_single fun i => key _
  refine ⟨?_, fun x φ h => ⟨φ.trans a, iso _ φ h, tor _ φ h _, tor _ φ h⟩⟩
  ext q
  constructor
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a.symm, e, iso' _ φ h⟩
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a, e, iso _ φ h⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsometStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  first | exact @GlobalTheory.trEll_latticeConj_move | exact GlobalTheory.trEll_latticeConj_move | (intros; apply GlobalTheory.trEll_latticeConj_move <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometry

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsomPhi

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (gam centMeas orbCls torEmb)

theorem tor_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : Tor P k) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem map_isHaar_rightInv {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (Tor P k)] [BorelSpace (Tor P k)]
    [IsTopologicalGroup (Tor P k)] (e : Tor P k ≃ₜ* H) (dt : Measure (Tor P k)) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant := by
  haveI h1 : (dt.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map dt e.toMulEquiv e.continuous e.symm.continuous
  refine ⟨h1, ⟨fun g => ?_⟩⟩
  have hc : (fun x : H => x * g) = fun x => g * x := funext fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tor_mul_comm]
  rw [hc]
  exact map_mul_left_eq_self _ g



open GlobalTheory.Orb in
theorem phi_map : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  intro D V V' r P v j hj μ dt f hμ hdt hok hok'
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  obtain ⟨hX, hmv⟩ := GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry _ _ D.sp.cm.sig hcm r V.rank V'.rank P V.gram V'.gram (frameLat V) (frameLat V')
    v j hj
  unfold Phi
  rw [← finsum_comp_equiv (Equiv.subtypeEquivRight (fun c => by rw [hX]))]
  refine finsum_congr fun q => ?_
  obtain ⟨c, h2⟩ := q
  obtain ⟨x, φ, hc, h⟩ := id h2
  subst hc
  obtain ⟨φ'', h'', hγ, ht⟩ := hmv x φ h
  obtain ⟨e, he, hme⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V.rank P V.gram (isHermND_gram V) (Fv D.host.F v) x φ h
  obtain ⟨e'', he'', hme''⟩ :=
    GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V'.rank P V'.gram (isHermND_gram V') (Fv D.host.F v) x φ'' h''
  haveI := hμ
  haveI := hdt
  obtain ⟨i1, i2⟩ := map_isHaar_rightInv P (Fv D.host.F v) e dt
  haveI : (centMeas h dt).IsHaarMeasure := by rw [hme dt]; exact i1
  haveI : (centMeas h dt).IsMulRightInvariant := by rw [hme dt]; exact i2
  have v1 := (hok.2 x φ h).orbInt_eq
  have v2 := (hok'.2 x φ'' h'').orbInt_eq
  have hm : centMeas h'' dt = (centMeas h dt).map (centEquiv j (gam h) hγ.symm) := by
    rw [hme'', hme dt, Measure.map_map (map_continuous (centEquiv j (gam h) hγ.symm)).measurable (map_continuous e).measurable]
    congr 1
    funext t
    apply Subtype.ext
    rw [he'', ht, ← he]
    rfl
  calc orbCls (J := V'.gram) (μ.map j) dt (f ∘ j.symm) ((Equiv.subtypeEquivRight (fun c => by rw [hX])) ⟨QuotientGroup.mk x, h2⟩)
      = orbInt (μ.map j) (gam h'') (centMeas h'' dt) (f ∘ j.symm) := v2.symm
    _ = orbInt (μ.map j) (gam h'') ((centMeas h dt).map (centEquiv j (gam h) hγ.symm)) (f ∘ j.symm) := by rw [hm]
    _ = orbInt μ (gam h) (centMeas h dt) ((f ∘ j.symm) ∘ j) := (hasOrbInt_map j hγ.symm (f ∘ j.symm) 0).2
    _ = orbInt μ (gam h) (centMeas h dt) f := by
      congr 1
      ext g
      simp
    _ = orbCls (J := V.gram) μ dt f ⟨QuotientGroup.mk x, h2⟩ := v1

end GlobalTheory.IsomPhi
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  first | exact @GlobalTheory.IsomPhi.phi_map | exact GlobalTheory.IsomPhi.phi_map | (intros; apply GlobalTheory.IsomPhi.phi_map <;> assumption)
end
end
