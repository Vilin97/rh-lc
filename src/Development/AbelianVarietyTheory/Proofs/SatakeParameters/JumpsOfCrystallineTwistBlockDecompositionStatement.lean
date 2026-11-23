module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsWithoutBlockNodupParametersStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockComplementIsSubAtEnlargement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.SubWp

theorem enl_loc_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    C.loc (twistM M χ) g =
      (C.inc.comp (Br.toLLK (D.nbr i w hw))) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (C.inc.comp (Br.toLLK (D.nbr i w hw))) := by
  refine Matrix.ext fun a b => ?_
  change C.inc ((D.nbr i w hw).toLL (((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i ((χ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i))) *
      C.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)))
  rw [Br.toLLK_alg, Br.toLLK_alg, ← map_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.SubWp

open GlobalTheory.SubWp in
theorem GlobalTheory.subWp_sub : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → IsSubOfSums (matRep (C.loc (WpO D.nd i ρ π))) (fun (_ : Unit) s => C.loc (rTwO D.nd i r π) s) := by
  intro D i w hw C r ρ π ⟨e, he⟩
  set f : KK D.nd i →+* ↥C.LL.1 := C.inc.comp (Br.toLLK (D.nbr i w hw)) with hf
  let A : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _)
  let B : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap)
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hRA : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * A = A * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
    intro g
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe,
      LinearMap.inl_apply]
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp <;> rfl
  refine ⟨1, fun _ => (), (LinearMap.pi fun _ => Matrix.mulVecLin (A.map f)), ?_, ?_⟩
  · intro v v' h
    have h1 := congrArg (fun z => (B.map f).mulVec (z 0)) h
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hBA,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mulVec] at h1
    exact h1
  · intro g v
    funext a
    simp only [LinearMap.pi_apply, Matrix.mulVecLin_apply]
    change (A.map f).mulVec ((C.loc (WpO D.nd i ρ π) g).mulVec v) = (C.loc (rTwO D.nd i r π) g).mulVec ((A.map f).mulVec v)
    rw [WpO, rTwO, enl_loc_eq, enl_loc_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← hf, ← Matrix.map_mul, ← Matrix.map_mul, hRA]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockComplementIsSubAtEnlargementStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.block_complement_isSub_at_enlargement : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → IsSubOfSums (matRep (C.loc (WpO D.nd i ρ π))) (fun (_ : Unit) s => C.loc (rTwO D.nd i r π) s) := by
  first | exact @GlobalTheory.subWp_sub | exact GlobalTheory.subWp_sub | (intros; apply GlobalTheory.subWp_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldEnlargementLocChiCyclotomic

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem enl_locChi_epsU : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  intro D i w hw C hC s
  rw [GlobalTheory.CycBridge.locChi_epsU D i w hw s]
  exact hC _

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldEnlargementLocChiCyclotomicStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  first | exact @GlobalTheory.HTW.Rec.enl_locChi_epsU | exact GlobalTheory.HTW.Rec.enl_locChi_epsU | (intros; apply GlobalTheory.HTW.Rec.enl_locChi_epsU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystallineStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.tateDual_matrixRep_continuous_crystalline : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  first | exact @GlobalTheory.HTW.Rec.tateDual_matRep_crys | exact GlobalTheory.HTW.Rec.tateDual_matRep_crys | (intros; apply GlobalTheory.HTW.Rec.tateDual_matRep_crys <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualsEqTateDualsAtEnlargement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section
namespace GlobalTheory.HTW.Rec

theorem enlLoc_apply {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (a b : Fin k) :
    C.loc M g a b = C.inc ((D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) := rfl

theorem twistedDuals_eq_tateDuals : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1)) → (∀ x, C.loc (rDuO D.nd i r x) = twistM (dualM (C.loc (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) ∧ C.loc (T2O D.nd i ρ π) = twistM (dualM (C.loc (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  intro D i w hw C r ρ π h
  have hc : ∀ g, ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) :=
    fun g => (h g).symm
  refine ⟨fun x => ?_, ?_⟩
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, rDuO, rTwO, map_inv, Units.val_mul, map_mul]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul, map_mul]
    exact congrArg _ (by ring)
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, T2O, map_inv, Units.val_mul, map_mul]

end GlobalTheory.HTW.Rec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualsEqTateDualsAtEnlargementStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDuals_eq_tateDuals_at_enlargement : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1)) → (∀ x, C.loc (rDuO D.nd i r x) = twistM (dualM (C.loc (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) ∧ C.loc (T2O D.nd i ρ π) = twistM (dualM (C.loc (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  first | exact @GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals | exact GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals | (intros; apply GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecomposition

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jumpIn_of_reads : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  intro D L C₀ i w hw C r ρ π ε κ hR hA hT hinc hc hcW hcr hS hτ
  have hε := GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic i w hw C hinc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedDuals_eq_tateDuals_at_enlargement i w hw C r ρ π hε
  have hO := goodO_finExt_integers (D.nd.l i) C.LL
  haveI : IsTopologicalRing ↥C.LL.1 := hO.2.2.2.1
  have hsub := GlobalTheory.T.block_complement_isSub_at_enlargement i w hw C r ρ π hS
  have hF : Formalism.MainNotions.LocalSituation.fontCore (Br.PD D.loc D.nbr i w hw) := hA (D.nd.l i) (D.nbr i w hw).Kw
  let A : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := Fin D.R.r → ↥C.LL.1
      ρ := matRep (C.loc (WpO D.nd i ρ π))
      cont := fun x => by
        change Continuous fun g => (C.loc (WpO D.nd i ρ π) g).mulVec x
        exact hcW.matrix_mulVec continuous_const }
  have hcrW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (WpO D.nd i ρ π))) :=
    GlobalTheory.CrysSub.isCrys_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) hF hO A
      (fun _ : Unit => C.loc (rTwO D.nd i r π)) (fun _ => hc π) hsub (fun _ => hcr π)
  have dual := fun x => GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (rTwO D.nd i r x)) hT (hc x) (hcr x)
  have dualW := GlobalTheory.T.tateDual_matrixRep_continuous_crystalline (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (WpO D.nd i ρ π)) hT hcW hcrW
  have uniq : ∀ τ g g', Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g →
      Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g' → g = g' := fun τ g g' hg hg' =>
    (GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host (D.nbr i w hw).Kw C.LL (Br.cEw D.nbr i w hw) κ τ).unique hg hg'
  refine ⟨fun x => ?_, fun x => ?_, fun x τ g hg => ?_, ?_, fun τ g hg u => ?_⟩
  · rw [h1 x]; exact (dual x).1
  · rw [h1 x]; exact (dual x).2
  · obtain ⟨g', hg', hj, -⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    exact fun a ha => hj x a ha
  · rw [h2]; exact dualW.2
  · obtain ⟨g', hg', -, hm⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    refine (hm u).trans ?_
    have hnd := GlobalTheory.T.jT2_hcAt_nodup_of_roomy L C₀ (liftIdx D i) g (pos ε g) hR
    split_ifs with hu
    · rw [Multiset.count_eq_one_of_mem hnd hu]; rfl
    · rw [Multiset.count_eq_zero_of_notMem hu]; rfl

end GlobalTheory.HTW.Rec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecompositionStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.jumpIn_of_reads | exact GlobalTheory.HTW.Rec.jumpIn_of_reads | (intros; apply GlobalTheory.HTW.Rec.jumpIn_of_reads <;> assumption)
end
end
