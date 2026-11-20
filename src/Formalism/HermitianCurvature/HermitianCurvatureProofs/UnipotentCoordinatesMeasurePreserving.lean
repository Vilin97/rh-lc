import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks

noncomputable section

section

open MeasureTheory Filter

namespace Formalism.FourierDecayAlt.P.Dx2.OrbJ

open Formalism.QuantumDeterminants

instance instBorelSS {k r : ℕ} : BorelSpace (Formalism.FourierDecayAlt.B.SS k r) := sorry

instance instBorelSSM {k r : ℕ} : BorelSpace (Formalism.FourierDecayAlt.B.SS k r × Mt k r) := sorry

section

variable {k r : ℕ}

theorem isUnit_of_N {g : Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ Nset k r) : IsUnit g.det := by sorry


theorem isUnit_of_G {g : Formalism.FourierDecayAlt.B.Mat k r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV k r) : IsUnit g.det := by sorry


theorem closedR {γ : Formalism.FourierDecayAlt.B.Mat k r} (hγ : IsUnit γ.det) :
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Formalism.FourierDecayAlt.C6.Rset γ) := by sorry


















theorem fmoc {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    IsFiniteMeasureOnCompacts μ := by sorry

theorem sigmaF {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    SigmaFinite μ := by sorry


theorem ae_mem {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by sorry


theorem contL (a : Formalism.FourierDecayAlt.B.Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by sorry



theorem contT (γ : Formalism.FourierDecayAlt.B.Mat k r) :
    Continuous fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1 := by sorry














end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem sfSS (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by sorry



theorem ae_inSS (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by sorry



















theorem mp_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) {ρ : Formalism.FourierDecayAlt.B.Mat k r}
    (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) : MeasurePreserving (Formalism.FourierDecayAlt.C6.actR γ ρ) D.μSS D.μSS := by sorry










theorem act_act (γ : Formalism.FourierDecayAlt.B.Mat k r) (hγ : IsUnit γ.det) {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : IsUnit ρ.det)
    (p : Formalism.FourierDecayAlt.B.SS k r) : Formalism.FourierDecayAlt.C6.actR γ ρ⁻¹ (Formalism.FourierDecayAlt.C6.actR γ ρ p) = p := by sorry











theorem lam_mul (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {g h : Formalism.FourierDecayAlt.B.Mat k r}
    (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    Formalism.FourierDecayAlt.B.lam k r z (g * h) = Formalism.FourierDecayAlt.B.lam k r z g + Formalism.FourierDecayAlt.B.lam k r z h := by sorry



theorem sgs_act (γ : Formalism.FourierDecayAlt.B.Mat k r) (hγ : IsUnit γ.det) {ρ : Formalism.FourierDecayAlt.B.Mat k r}
    (hρu : IsUnit ρ.det) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.B.sgs (Formalism.FourierDecayAlt.C6.actR γ ρ p) γ = Formalism.FourierDecayAlt.B.sgs p γ := by sorry






theorem xiTau_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) (p : Formalism.FourierDecayAlt.B.SS k r)
    (hn : Matrix.of p.1.2 ∈ Nset k r) (hn' : Matrix.of p.2.2 ∈ Nset k r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) (Formalism.FourierDecayAlt.C6.actR γ ρ p) = Formalism.FourierDecayAlt.B.xiTau D (1, 1) p := by sorry




















theorem integrand_act (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    {ρ : Formalism.FourierDecayAlt.B.Mat k r} (hρ : ρ ∈ Formalism.FourierDecayAlt.C6.Rset γ) (p : Formalism.FourierDecayAlt.B.SS k r)
    (hn : Matrix.of p.1.2 ∈ Nset k r) (hn' : Matrix.of p.2.2 ∈ Nset k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ F (Formalism.FourierDecayAlt.C6.actR γ ρ p) = Formalism.FourierDecayAlt.D.orbIntegrand D γ F p := by sorry






theorem fub (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μR : Measure (Mt k r))
    [SigmaFinite μR] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : Formalism.FourierDecayAlt.B.SS k r → E) (hG : Integrable G D.μSS)
    (θ' : Formalism.FourierDecayAlt.B.SS k r → ℝ) (hθ' : Formalism.FourierDecayAlt.D.IsNormCut D γ μR θ') :
    Integrable (fun z : Formalism.FourierDecayAlt.B.SS k r × Mt k r => θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of z.2) z.1) • G z.1)
        (D.μSS.prod μR) ∧
      ∫ p, G p ∂D.μSS = ∫ x, ∫ p, θ' (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) • G p ∂D.μSS ∂μR := by sorry



































end

end Formalism.FourierDecayAlt.P.Dx2.OrbJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Dx2.OrbJ

theorem orbital_integral_indep_choice : Formalism.FourierDecayAlt.D.OrbJIndep := by sorry

















































end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.Dx2.MN

variable {k ρ : ℕ}

theorem eB_mid (i : Fin (2 * ρ + k + 1)) : U.eB k 1 ρ (Sum.inl (Sum.inr i)) = levPos k 1 ρ i := by sorry


theorem eB_first_val : (U.eB k 1 ρ (Sum.inl (Sum.inl 0))).val = 0 := by sorry

theorem eB_last_eq : U.eB k 1 ρ (Sum.inr 0) = B2x4.lastI k ρ := by sorry


theorem herm_bvec_lift (y : Fin (2 * ρ + k + 1) → ℂ) (q : Fin (2 * (1 + ρ) + k + 1)) :
    herm (Hpk k (1 + ρ)) (bvec q) (liftVec k 1 ρ y) = ∑ j, star (y j) * Hpk k (1 + ρ) (levPos k 1 ρ j) q := by sorry






theorem hpk_lev_first (j : Fin (2 * ρ + k + 1)) (q : Fin (2 * (1 + ρ) + k + 1)) (hq : q.val = 0) :
    Hpk k (1 + ρ) (levPos k 1 ρ j) q = 0 := by sorry




theorem hpk_lev_last (j : Fin (2 * ρ + k + 1)) :
    Hpk k (1 + ρ) (levPos k 1 ρ j) (B2x4.lastI k ρ) = 0 := by sorry




theorem herm_self_real (y : Fin (2 * ρ + k + 1) → ℂ) :
    (((herm (Hpk k ρ) y y).re : ℝ) : ℂ) = herm (Hpk k ρ) y y := by sorry








theorem cHc (c : Matrix (Fin (2 * ρ + k + 1)) (Fin 1) ℂ) :
    (cᴴ * Hpk k ρ * c) 0 0 = herm (Hpk k ρ) (fun i => c i 0) (fun i => c i 0) := by sorry





theorem rn_heis (x : U.RC k 1 ρ) : U.Rn k 1 ρ x = B2.heis0 k ρ (fun i => x.1 i 0, x.2.2 0) := by sorry








































































































theorem embG_eq (y : B.Mat k ρ) : U.embG k 1 ρ y = ιLev k 1 ρ y := by sorry









def heisM (x : B2.HPar k ρ) : Mt k (1 + ρ) := sorry

def castMt {a b : ℕ} (h : a = b) (x : Mt k a) : Mt k b := sorry

theorem castM_rfl {a : ℕ} (g : B.Mat k a) : D.castM rfl g = g := by sorry


theorem haar_cast {a b : ℕ} (h : a = b) (μ : Measure (Mt k a)) (hμ : B.IsHaarOn (Nset k a) μ) :
    B.IsHaarOn (Nset k b) (μ.map (castMt h)) := by sorry





instance isEmpty_upperTriangular_one : IsEmpty (G.UT 1) := sorry




def phi (x : U.RC k 1 ρ) : B2.HPar k ρ := sorry

theorem phi_mp : MeasurePreserving (phi (k := k) (ρ := ρ)) volume volume := by sorry















theorem castMt_cont {a b : ℕ} (h : a = b) : Continuous (castMt (k := k) h) := by sorry





theorem muN_succ (ρ : ℕ) [SigmaFinite (D.muN k ρ)] :
    D.muN k (ρ + 1) =
      (((B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ))).map B2.mulM).map (castMt (Nat.add_comm 1 ρ)) := by sorry





















theorem sigma_of_haar {a : ℕ} {S : Set (B.Mat k a)} {μ : Measure (Mt k a)} (h : B.IsHaarOn S μ) : SigmaFinite μ := by sorry



theorem haar_zero : B.IsHaarOn (Nset k 0) (D.muN k 0) := by sorry

















theorem haar : ∀ r : ℕ, B.IsHaarOn (Nset k r) (D.muN k r)
  | 0 => haar_zero
  | ρ + 1 => by
    have ih := by sorry




end Formalism.FourierDecayAlt.P.Dx2.MN

end

section

open MeasureTheory Module Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.Dx2.NH

theorem finrank_CV (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℝ (J.CV E) = 2 * S6.deg E := by sorry




theorem nhat : D.NhatCovol := by sorry

































end Formalism.FourierDecayAlt.P.Dx2.NH

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.Tower

variable {k : ℕ}

theorem lev_eq_embG (o ρ : ℕ) (y : B.Mat k ρ) : ιLev k o ρ y = U.embG k o ρ y := by sorry









theorem lev_one (o ρ : ℕ) : ιLev k o ρ (1 : B.Mat k ρ) = 1 := by sorry


theorem lev_mul (o ρ : ℕ) (a b : B.Mat k ρ) : ιLev k o ρ (a * b) = ιLev k o ρ a * ιLev k o ρ b := by sorry



theorem lev_GV (o ρ : ℕ) (y : B.Mat k ρ) (hy : y ∈ B.GV k ρ) : ιLev k o ρ y ∈ B.GV k (o + ρ) := by sorry


theorem lev_cont (o ρ : ℕ) : Continuous (ιLev k o ρ) := by sorry





theorem sum_lift_gen (o ρ : ℕ) (F : Fin (2 * (o + ρ) + k + 1) → ℂ)
    (h : ∀ p : Fin (2 * (o + ρ) + k + 1), ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o) → F p = 0) :
    ∑ p, F p = ∑ j : Fin (2 * ρ + k + 1), F (levPos k o ρ j) := by sorry














theorem liftVec_levPos_gen (o ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (2 * ρ + k + 1)) :
    liftVec k o ρ v (levPos k o ρ j) = v j := by sorry





theorem liftVec_out_gen (o ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) (p : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : liftVec k o ρ v p = 0 := by sorry


theorem lev_levPos (o ρ : ℕ) (y : B.Mat k ρ) (i j : Fin (2 * ρ + k + 1)) :
    ιLev k o ρ y (levPos k o ρ i) (levPos k o ρ j) = y i j := by sorry





theorem lev_out_row (o ρ : ℕ) (y : B.Mat k ρ) (p q : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y p q = if p = q then 1 else 0 := by sorry


theorem lev_out_col (o ρ : ℕ) (y : B.Mat k ρ) (p q : Fin (2 * (o + ρ) + k + 1))
    (hq : ¬ (o ≤ q.val ∧ q.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y p q = if p = q then 1 else 0 := by sorry





theorem lev_mulVec_lift (o ρ : ℕ) (y : B.Mat k ρ) (v : Fin (2 * ρ + k + 1) → ℂ) :
    ιLev k o ρ y *ᵥ liftVec k o ρ v = liftVec k o ρ (y *ᵥ v) := by sorry















theorem lev_mulVec_out (o ρ : ℕ) (y : B.Mat k ρ) (p : Fin (2 * (o + ρ) + k + 1))
    (hp : ¬ (o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o)) : ιLev k o ρ y *ᵥ bvec p = bvec p := by sorry





theorem bvec_levPos (o ρ : ℕ) (j : Fin (2 * ρ + k + 1)) : bvec (levPos k o ρ j) = liftVec k o ρ (bvec j) := by sorry













theorem lev_UW (o ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) (hg : g ∈ UWset k ρ z) :
    ιLev k o ρ g ∈ UWset k (o + ρ) (liftVec k o ρ z) := by sorry













theorem castM_one {a b : ℕ} (h : a = b) : D.castM (k := k) h 1 = 1 := by sorry


theorem castM_mul {a b : ℕ} (h : a = b) (x y : B.Mat k a) : D.castM h (x * y) = D.castM h x * D.castM h y := by sorry


theorem castV_rfl {a : ℕ} (v : Fin (2 * a + k + 1) → ℂ) : D.castV (rfl : a = a) v = v := by sorry


theorem castM_UW {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by sorry


theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by sorry




theorem herm_wb {m : ℕ} (v : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) :
    herm (Hpk k m) v v = herm (Hb k) (wbPart k m v) (wbPart k m v) := by sorry



theorem Tz_eq {m m' : ℕ} (v : Fin (2 * m + k + 1) → ℂ) (v' : Fin (2 * m' + k + 1) → ℂ) (hv : inWb k m v)
    (hv' : inWb k m' v') (h : wbPart k m v = wbPart k m' v') : Tz k m v = Tz k m' v' := by sorry


def zL {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * ρ + k + 1) → ℂ := sorry


theorem zL_wb {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    inWb k ρ (zL o ρ h z) := by sorry


theorem zL_wbPart {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) :
    wbPart k ρ (zL o ρ h z) = wbPart k r z := by sorry


theorem zL_Tz {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    Tz k ρ (zL o ρ h z) = Tz k r z := by sorry


theorem lift_zL {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    D.castV h (liftVec k o ρ (zL o ρ h z)) = z := by sorry







theorem haar_norm {a : ℕ} {U : Set (B.Mat k a)} {μ : Measure (Mt k a)} (hμ : B.IsHaarOn U μ)
    (hU : IsCompact U) : B.IsHaarOn U ((μ Set.univ)⁻¹ • μ) ∧ ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by sorry


















theorem mem_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : B.Mat k ρ) (ha : a ∈ UWset k ρ (zL o ρ h z)) : D.castM h (ιLev k o ρ a) ∈ UWset k r z := by sorry



theorem rep_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (π : B.Mat k r → (E →L[ℂ] E))
    (hπ : IsCRepOn (UWset k r z) π) :
    IsCRepOn (UWset k ρ (zL o ρ h z)) (fun y => π (D.castM h (ιLev k o ρ y))) := by sorry





theorem sec_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (hz' : inWb k r z') (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hs : IsSection k r z z' μsec) :
    IsSection k ρ (zL o ρ h z) (zL o ρ h z') μsec := by sorry




def wMeas {m : ℕ} (z : Fin (2 * m + k + 1) → ℂ) (hz : inWb k m z) (hT : 0 < Tz k m z) : Measure (Mt k m) := sorry


theorem wMeas_spec {m : ℕ} (z : Fin (2 * m + k + 1) → ℂ) (hz : inWb k m z) (hT : 0 < Tz k m z) :
    B.IsHaarOn (UWset k m z) (wMeas z hz hT) ∧ wMeas z hz hT Set.univ = 1 := by sorry


variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def lvl {r : ℕ} (S : B.RealPlaceData k r Wp Wq) (o ρ : ℕ) (h : o + ρ = r) : B.RealPlaceData k ρ Wp Wq where
  z := sorry































def tower {r : ℕ} (S : B.RealPlaceData k r Wp Wq) : ∀ j : ℕ, B.RealPlaceData k (r - j) Wp Wq
  | 0 => S
  | j + 1 => lvl S (min (j + 1) r) (r - (j + 1)) (by omega)

theorem lift_zL' {r : ℕ} (o o' ρ : ℕ) (e : o = o') (h : o + ρ = r) (h' : o' + ρ = r)
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    D.castV h' (liftVec k o' ρ (zL o ρ h z)) = z := by sorry


theorem castM_lev_congr {r : ℕ} (o o' ρ : ℕ) (e : o = o') (h : o + ρ = r) (h' : o' + ρ = r) (y : B.Mat k ρ) :
    D.castM h (ιLev k o ρ y) = D.castM h' (ιLev k o' ρ y) := by sorry


theorem castVec_liftVec_zero_level {r : ℕ} (h : 0 + r = r) (z : Fin (2 * r + k + 1) → ℂ) : D.castV h (liftVec k 0 r z) = z := by sorry





theorem castMat_levelEmbed_zero {r : ℕ} (h : 0 + r = r) (y : B.Mat k r) : D.castM h (ιLev k 0 r y) = y := by sorry





theorem towerExists : Formalism.FourierDecayAlt.D.TowerExists := by sorry





























end Formalism.FourierDecayAlt.P.Dx2.Tower

end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace Formalism.FourierDecayAlt.P.Dx2.DF

variable {k r : ℕ}

abbrev ee (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) → ℂ := sorry

abbrev es (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) → ℂ := sorry

theorem herm_bvec_right (x : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec p) = ∑ j, Hpk k r p j * x j := by sorry


theorem hpk_eI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by sorry




theorem hpk_esI (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by sorry




theorem herm_ee (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) x (ee k r a) = x (esI k r a) := by sorry


theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) x (es k r a) = x (eI k r a) := by sorry


theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by sorry



theorem eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by sorry




theorem esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by sorry





@[simp] theorem h_ee_ee (a b : Fin r) : herm (Hpk k r) (ee k r a) (ee k r b) = 0 := by sorry


@[simp] theorem h_ee_es (a b : Fin r) : herm (Hpk k r) (ee k r a) (es k r b) = if a = b then 1 else 0 := by sorry


@[simp] theorem h_es_ee (a b : Fin r) : herm (Hpk k r) (es k r a) (ee k r b) = if a = b then 1 else 0 := by sorry


@[simp] theorem h_es_es (a b : Fin r) : herm (Hpk k r) (es k r a) (es k r b) = 0 := by sorry


theorem wb_eI {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) : w (eI k r a) = 0 := by sorry


theorem wb_esI {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) : w (esI k r a) = 0 := by sorry


theorem herm_symm' (u w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) w u = star (herm (Hpk k r) u w) := by sorry


@[simp] theorem h_w_ee {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) w (ee k r a) = 0 := by sorry

@[simp] theorem h_w_es {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) w (es k r a) = 0 := by sorry

@[simp] theorem h_ee_w {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) (ee k r a) w = 0 := by sorry

@[simp] theorem h_es_w {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (a : Fin r) :
    herm (Hpk k r) (es k r a) w = 0 := by sorry

theorem herm_self_alt {z : Fin (2 * r + k + 1) → ℂ} : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by sorry





section iso

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℂ) (w : Fin m → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by sorry


theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin m → ℂ) (v : Fin m → ℂ) :
    herm H v (∑ i ∈ s, f i) = ∑ i ∈ s, herm H v (f i) := by sorry


variable {ι : Type*} [Fintype ι]

def smap (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) : Fin m → ℂ := sorry

theorem smap_iso (hH : Hᴴ = H) (u w Y : ι → Fin m → ℂ)
    (h2 : ∀ x j, herm H x (u j) = ∑ i, herm H x (w i) * herm H (u i) (u j))
    (h3 : ∀ i j, herm H (Y i) (Y j) = herm H (u i) (u j))
    (h4 : ∀ x, (∀ j, herm H x (u j) = 0) → ∀ i, herm H x (Y i) = 0)
    (x y : Fin m → ℂ) : herm H (smap H u w Y x) (smap H u w Y y) = herm H x y := by sorry




































theorem smap_apply_u (u w Y : ι → Fin m → ℂ) [DecidableEq ι]
    (h1 : ∀ i j, herm H (u i) (w j) = if i = j then 1 else 0) (i : ι) : smap H u w Y (u i) = Y i := by sorry



theorem smap_fix (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) (hx : ∀ i, herm H x (w i) = 0) :
    smap H u w Y x = x := by sorry


def smat (u w Y : ι → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ := sorry

theorem smat_mulVec (u w Y : ι → Fin m → ℂ) (x : Fin m → ℂ) : smat H u w Y *ᵥ x = smap H u w Y x := by sorry











end iso

theorem smat_UH {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) {ι : Type*} [Fintype ι] (u w Y : ι → Fin m → ℂ)
    (h2 : ∀ x j, herm H x (u j) = ∑ i, herm H x (w i) * herm H (u i) (u j))
    (h3 : ∀ i j, herm H (Y i) (Y j) = herm H (u i) (u j))
    (h4 : ∀ x, (∀ j, herm H x (u j) = 0) → ∀ i, herm H x (Y i) = 0) : smat H u w Y ∈ UH H := by sorry





section weyl

variable {k r : ℕ} (π : Equiv.Perm (Fin (r + 1)))

def piX (b : Fin r) : Fin r := sorry

theorem piX_spec (b : Fin r) (h : π b.castSucc ≠ Fin.last r) : (piX π b).castSucc = π b.castSucc := by sorry


theorem piX_inj {b c : Fin r} (hb : π b.castSucc ≠ Fin.last r) (hc : π c.castSucc ≠ Fin.last r) :
    piX π b = piX π c ↔ b = c := by sorry







theorem piX_ne {b a : Fin r} (hb : π b.castSucc ≠ Fin.last r) (ha : π (Fin.last r) = a.castSucc) : piX π b ≠ a := by sorry





end weyl

section caseA

variable {k r : ℕ}

def uB (z' ν' : Fin (2 * r + k + 1) → ℂ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => ee k r b
  | Sum.inl (Sum.inr b) => es k r b
  | Sum.inr j => ![z', ν'] j

def wB (z' ν' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => es k r b
  | Sum.inl (Sum.inr b) => ee k r b
  | Sum.inr j => ![(-(1 / (s : ℂ) ^ 2)) • z', ν'] j

variable {z' ν' : Fin (2 * r + k + 1) → ℂ} {s : ℝ}

theorem herm_neg_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) : herm H u (-w) = -herm H u w := by sorry


theorem herm_neg_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u w : Fin m → ℂ) : herm H (-u) w = -herm H u w := by sorry


theorem herm_rsmul_left {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : ℝ) (u w : Fin m → ℂ) :
    herm H (a • u) w = (a : ℂ) * herm H u w := by sorry



theorem herm_rsmul_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (a : ℝ) (u w : Fin m → ℂ) :
    herm H u (a • w) = (a : ℂ) * herm H u w := by sorry




theorem inWb_smul {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (c : ℂ) : inWb k r (c • w) := by sorry


theorem herm_zν (hνz : herm (Hpk k r) ν' z' = 0) : herm (Hpk k r) z' ν' = 0 := by sorry


theorem uw_dual (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (uB z' ν' i) (wB z' ν' s j) = if i = j then 1 else 0 := by sorry







theorem uw_complete (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (x : Fin (2 * r + k + 1) → ℂ) (j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (uB z' ν' j) =
      ∑ i, herm (Hpk k r) x (wB z' ν' s i) * herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by sorry







variable (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)

def YA (z' ν' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) (a0 b0 : Fin r) :
    (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => if b = b0 then (d b0.castSucc / (s : ℂ)) • (ν' - (s : ℂ)⁻¹ • z')
      else d b.castSucc • es k r (piX π b)
  | Sum.inl (Sum.inr b) => if b = b0 then (2 * conj (d b0.castSucc))⁻¹ • (z' + (s : ℂ) • ν')
      else (conj (d b.castSucc))⁻¹ • ee k r (piX π b)
  | Sum.inr j => ![d (Fin.last r) • es k r a0 - ((s : ℂ) ^ 2 / (2 * conj (d (Fin.last r)))) • ee k r a0,
      ((s : ℂ) / (2 * conj (d (Fin.last r)))) • ee k r a0 + (d (Fin.last r) / (s : ℂ)) • es k r a0] j

theorem YA_gram (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (hd : ∀ a, d a ≠ 0) (a0 b0 : Fin r)
    (ha : π (Fin.last r) = a0.castSucc) (hb : π b0.castSucc = Fin.last r) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (YA π d z' ν' s a0 b0 i) (YA π d z' ν' s a0 b0 j) =
      herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by sorry
































































theorem YA_perp (a0 b0 : Fin r) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (YA π d z' ν' s a0 b0 i) = 0 := by sorry









theorem piX_injB (hB : π (Fin.last r) = Fin.last r) (b c : Fin r) : piX π b = piX π c ↔ b = c := by sorry




def YB (z' ν' : Fin (2 * r + k + 1) → ℂ) (s κ : ℝ) : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ
  | Sum.inl (Sum.inl b) => d b.castSucc • es k r (piX π b)
  | Sum.inl (Sum.inr b) => (conj (d b.castSucc))⁻¹ • ee k r (piX π b)
  | Sum.inr j => ![(d (Fin.last r) / (s : ℂ) ^ 2) • (((κ : ℂ) * (s : ℂ) ^ 2) • ν' - z'),
      (d (Fin.last r) / (s : ℂ) ^ 2) • (ν' - (κ : ℂ) • z')] j

theorem YB_gram (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (hd : ∀ a, d a ≠ 0) (κ : ℝ)
    (hκ : (κ : ℂ) ^ 2 * (s : ℂ) ^ 2 * (d (Fin.last r) * conj (d (Fin.last r))) =
      d (Fin.last r) * conj (d (Fin.last r)) - (s : ℂ) ^ 4)
    (hB : π (Fin.last r) = Fin.last r) (i j : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) (YB π d z' ν' s κ i) (YB π d z' ν' s κ j) =
      herm (Hpk k r) (uB z' ν' i) (uB z' ν' j) := by sorry















end caseA

section sigma

variable {k r : ℕ} {z' ν' : Fin (2 * r + k + 1) → ℂ} {s : ℝ}

theorem YB_perp (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (κ : ℝ) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    herm (Hpk k r) x (YB π d z' ν' s κ i) = 0 := by sorry









variable (Y : (Fin r ⊕ Fin r) ⊕ Fin 2 → Fin (2 * r + k + 1) → ℂ)

theorem sig_UH (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1)
    (h3 : ∀ i j, herm (Hpk k r) (Y i) (Y j) = herm (Hpk k r) (uB z' ν' i) (uB z' ν' j))
    (h4 : ∀ x, (∀ j, herm (Hpk k r) x (uB z' ν' j) = 0) → ∀ i, herm (Hpk k r) x (Y i) = 0) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y ∈ UH (Hpk k r) := by sorry


theorem sig_u (hz : inWb k r z') (hν : inWb k r ν') (hs : 0 < s)
    (hzz : herm (Hpk k r) z' z' = -((s : ℂ) ^ 2)) (hνz : herm (Hpk k r) ν' z' = 0)
    (hνν : herm (Hpk k r) ν' ν' = 1) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y *ᵥ uB z' ν' i = Y i := by sorry


theorem sig_fix (x : Fin (2 * r + k + 1) → ℂ) (hx : ∀ i, herm (Hpk k r) x (wB z' ν' s i) = 0) :
    smat (Hpk k r) (uB z' ν') (wB z' ν' s) Y *ᵥ x = x := by sorry


end sigma

section frame

variable {k r : ℕ}

def Wb (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := sorry

theorem prW_eq (z v : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z v = Wb v - (herm (Hpk k r) (Wb v) z / herm (Hpk k r) z z) • z := by sorry

theorem Wb_of_inWb {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : Wb w = w := by sorry




theorem inWb_of_coords {w : Fin (2 * r + k + 1) → ℂ} (h1 : ∀ a : Fin r, w (eI k r a) = 0)
    (h2 : ∀ a : Fin r, w (esI k r a) = 0) : inWb k r w := by sorry








theorem decomp (v : Fin (2 * r + k + 1) → ℂ) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + (∑ a : Fin r, v (esI k r a) • es k r a) + Wb v := by sorry

































theorem Wb_add (v w : Fin (2 * r + k + 1) → ℂ) : Wb (v + w) = Wb v + Wb w := by sorry


theorem Wb_smul (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) : Wb (c • v) = c • Wb v := by sorry


theorem Wb_sum {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    Wb (∑ i ∈ s, f i) = ∑ i ∈ s, Wb (f i) := by sorry


theorem Wb_ee (a : Fin r) : Wb (ee k r a) = 0 := by sorry




theorem Wb_es (a : Fin r) : Wb (es k r a) = 0 := by sorry




variable (m₀ : B.Mat k r) (hmU : m₀ ∈ UH (Hpk k r)) (hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a)
  (hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a)

include hmU in
theorem herm_m0_mulVec_invariant (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (m₀ *ᵥ v) (m₀ *ᵥ w) = herm (Hpk k r) v w := by sorry


include hmU hme hms in
theorem m0_mulVec_mem_orthogonal {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) : inWb k r (m₀ *ᵥ w) := by sorry




include hmU hme hms in
theorem reflection_commutes_m0_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Wb (m₀ *ᵥ v) = m₀ *ᵥ Wb v := by sorry







include hmU hme hms in

theorem orthoProj_m0_intertwine {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (μ : ℝ) (hμ : μ ≠ 0)
    (hmz : m₀ *ᵥ z' = (μ : ℂ) • z) (hzz : herm (Hpk k r) z' z' ≠ 0) (v : Fin (2 * r + k + 1) → ℂ) :
    D.prW k r z (m₀ *ᵥ v) = m₀ *ᵥ D.prW k r z' v := by sorry











end frame

section prWlin

variable {k r : ℕ}

theorem prW_add (z v w : Fin (2 * r + k + 1) → ℂ) : D.prW k r z (v + w) = D.prW k r z v + D.prW k r z w := by sorry


theorem prW_smul (z v : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : D.prW k r z (c • v) = c • D.prW k r z v := by sorry


theorem prW_sub (z v w : Fin (2 * r + k + 1) → ℂ) : D.prW k r z (v - w) = D.prW k r z v - D.prW k r z w := by sorry


theorem prW_self {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0) :
    D.prW k r z z = 0 := by sorry


theorem prW_perp {z ν : Fin (2 * r + k + 1) → ℂ} (hν : inWb k r ν) (hνz : herm (Hpk k r) ν z = 0) :
    D.prW k r z ν = ν := by sorry


end prWlin

section adj

theorem monomialMatrix_inv {m : ℕ} (π : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP π d)⁻¹ = Matrix.of fun b i => if π b = i then (d b)⁻¹ else 0 := by sorry












theorem monomialMatrix_adj {m : ℕ} (π : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) (b i : Fin m) :
    (C2.monoP π d).adjugate b i = (C2.monoP π d).det * (if π b = i then (d b)⁻¹ else 0) := by sorry



















end adj

section assemble

variable {k r : ℕ}

theorem mul_UH {m₀ σ : B.Mat k r} (h1 : m₀ ∈ UH (Hpk k r)) (h2 : σ ∈ UH (Hpk k r)) : m₀ * σ ∈ UH (Hpk k r) := by sorry







theorem fvec_cs (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = ee k r a := by sorry


theorem fvec_lastI (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by sorry


theorem reduced_matrix_of_stabilizer {z z' : Fin (2 * r + k + 1) → ℂ} (m₀ σ : B.Mat k r) (hmU : m₀ ∈ UH (Hpk k r))
    (hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a) (μ : ℝ) (hμ : μ ≠ 0) (hmz : m₀ *ᵥ z' = (μ : ℂ) • z)
    (a b : Fin (r + 1)) :
    Zhat k r z z' (m₀ * σ) a b = herm (Hpk k r) (σ *ᵥ fvec k r z' b) (fvec k r ((μ : ℂ)⁻¹ • z') a) := by sorry








end assemble

section caseAmain

variable {k r : ℕ}

theorem cast_or_last (b : Fin (r + 1)) : b = Fin.last r ∨ ∃ b' : Fin r, b = b'.castSucc := by sorry




theorem caseA {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (a0 b0 : Fin r) (ha : π (Fin.last r) = a0.castSucc)
    (hb : π b0.castSucc = Fin.last r) :
    ∃ γ ∈ B.GV k r, Zhat k r S.z S.z' γ = C2.monoP π d0 ∧ Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ := by sorry



























































































































































































theorem caseB {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    ∃ γ ∈ B.GV k r, Zhat k r S.z S.z' γ = C2.monoP π d0 ∧ Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ := by sorry






























































































































































































end caseAmain

end Formalism.FourierDecayAlt.P.Dx2.DF

namespace Formalism.FourierDecayAlt.P.Dx2

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

section final

theorem ptMatN_mono (p : C.LPt) (n : ℕ) (hn : D.ptSize p = n) (hp : ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) :
    ∃ (π : Equiv.Perm (Fin n)) (d : Fin n → ℂ), (∀ a, d a ≠ 0) ∧ D.ptMatN p n = C2.monoP π d := by sorry




theorem det_monomialMatrix_last {r : ℕ} (π : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (hB : π (Fin.last r) = Fin.last r) :
    (C2.monoP π d).det = d (Fin.last r) * ((C2.monoP π d).submatrix Fin.castSucc Fin.castSucc).det := by sorry







theorem dFrameExists : Formalism.FourierDecayAlt.D.DFrameExists := by sorry























end final

end Formalism.FourierDecayAlt.P.Dx2

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.Split

variable {k j ρ : ℕ}

def c1v (x1 : U.RC k 1 (j + ρ)) : Fin (2 * (j + ρ) + k + 1) → ℂ := sorry
def cX (x1 : U.RC k 1 (j + ρ)) : Fin j → ℂ := sorry
def cV (x1 : U.RC k 1 (j + ρ)) : Fin (2 * ρ + k + 1) → ℂ := sorry
def cS (x1 : U.RC k 1 (j + ρ)) : Fin j → ℂ := sorry
def s1 (x1 : U.RC k 1 (j + ρ)) : ℝ := sorry

def nc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Fin j → ℂ := sorry


def q2L (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : ℝ := sorry



def Cm (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Matrix (Fin (2 * ρ + k + 1)) (Fin (j + 1)) ℂ := sorry


def Sm (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ := sorry




def Um (x1 : U.RC k 1 (j + ρ)) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ := sorry




def Ut0 (x1 : U.RC k 1 (j + ρ)) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ := sorry




def TX (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : U.RC k (j + 1) ρ := sorry


def TU (x1 : U.RC k 1 (j + ρ)) : G.UT (j + 1) → ℂ := sorry

theorem skew_diag_re (q : (G.UT j → ℂ) × (Fin j → ℝ)) (a : Fin j) : (U.skewOf q a a).re = 0 := by sorry


theorem skewOf_TX (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) : U.skewOf (TX x1 x).2 = Sm x1 x := by sorry






























theorem um_uni (x1 : U.RC k 1 (j + ρ)) : Ux2.uniK (Ux2.kU (j + 1)) (Um x1) := by sorry















theorem rev_zero' (n : ℕ) : Fin.rev (0 : Fin (n + 1)) = Fin.last n := by sorry
theorem rev_succ' {n : ℕ} (a : Fin n) : Fin.rev a.succ = (Fin.rev a).castSucc := by sorry
theorem rev_last' (n : ℕ) : Fin.rev (Fin.last n) = 0 := by sorry
theorem rev_castSucc' {n : ℕ} (a : Fin n) : Fin.rev a.castSucc = (Fin.rev a).succ := by sorry

theorem wvec_apply (v : Fin j → ℂ) (a : Fin j) : (G.wMat j *ᵥ v) a = v a.rev := by sorry


theorem vecMul_w_apply (v : Fin j → ℂ) (a : Fin j) : Matrix.vecMul v (G.wMat j) a = v a.rev := by sorry







theorem mul_w_apply {n : ℕ} {m : Type*} (A : Matrix m (Fin n) ℂ) (a : m) (b : Fin n) :
    (A * G.wMat n) a b = A a b.rev := by sorry






theorem w_conj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (G.wMat n * M * G.wMat n) a b = M a.rev b.rev := by sorry


theorem um_ct_mul (x1 : U.RC k 1 (j + ρ)) :
    (Um x1)ᴴ * (G.wMat (j + 1) * Ut0 x1 * G.wMat (j + 1)) = 1 := by sorry


























theorem ut_eq (x1 : U.RC k 1 (j + ρ)) :
    G.wMat (j + 1) * (Um x1)ᴴ⁻¹ * G.wMat (j + 1) = Ut0 x1 := by sorry




theorem castM_apply {a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by sorry


theorem hh (k j ρ : ℕ) : 2 * ((j + 1) + ρ) + k + 1 = 2 * (1 + (j + ρ)) + k + 1 := by sorry

theorem pos0 : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl 0))) = U.eB k 1 (j + ρ) (Sum.inl (Sum.inl 0)) := by sorry


theorem posX (a : Fin j) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inl a.succ))) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inl (Sum.inl a))))) := by sorry


theorem posV (v : Fin (2 * ρ + k + 1)) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inl (Sum.inr v))) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inl (Sum.inr v))))) := by sorry


theorem posS (b : Fin j) : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inr b.castSucc)) =
    U.eB k 1 (j + ρ) (Sum.inl (Sum.inr (U.eB k j ρ (Sum.inr b)))) := by sorry


theorem posL : Fin.cast (hh k j ρ) (U.eB k (j + 1) ρ (Sum.inr (Fin.last j))) = U.eB k 1 (j + ρ) (Sum.inr 0) := by sorry


theorem lhs_form (x1 : U.RC k 1 (j + ρ)) (Q : B.Mat k (j + ρ)) :
    U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) Q =
      U.blk3 1 (-(G.wMat 1 * (Matrix.of x1.1)ᴴ * Hpk k (j + ρ)) * Q)
        (G.wMat 1 * ((-(1 / 2 : ℂ)) • ((Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Matrix.of x1.1) + U.skewOf x1.2))
        0 Q (Matrix.of x1.1) 0 0 1 := by sorry



theorem rhs_form (X : U.RC k (j + 1) ρ) (V : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) :
    U.Rn k (j + 1) ρ X * U.muP k (j + 1) ρ V =
      U.blk3 V (-(G.wMat (j + 1) * (Matrix.of X.1)ᴴ * Hpk k ρ))
        (G.wMat (j + 1) * ((-(1 / 2 : ℂ)) • ((Matrix.of X.1)ᴴ * Hpk k ρ * Matrix.of X.1) + U.skewOf X.2) *
          (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1)))
        0 1 (Matrix.of X.1 * (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1))) 0 0 (G.wMat (j + 1) * Vᴴ⁻¹ * G.wMat (j + 1)) := by sorry



theorem hrn_form (x : U.RC k j ρ) :
    Hpk k (j + ρ) * U.Rn k j ρ x =
      U.blk3 0 0 (G.wMat j) 0 (Hpk k ρ) (Hpk k ρ * Matrix.of x.1) (G.wMat j) (-((Matrix.of x.1)ᴴ * Hpk k ρ))
        ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2) := by sorry



theorem vecMul_block3_first_coords (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (a : Fin j) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inl (Sum.inl a))) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A11 a +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A21 a +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A31 a := by sorry





theorem vecMul_block3_middle_coords (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (v : Fin (2 * ρ + k + 1)) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inl (Sum.inr v))) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A12 v +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A22 v +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A32 v := by sorry





theorem vecMul_block3_last_coord (y : Fin (2 * (j + ρ) + k + 1) → ℂ)
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (b : Fin j) :
    Matrix.vecMul y (U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) (U.eB k j ρ (Sum.inr b)) =
      Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inl (Sum.inl a)))) A13 b +
        Matrix.vecMul (fun v => y (U.eB k j ρ (Sum.inl (Sum.inr v)))) A23 b +
        Matrix.vecMul (fun a => y (U.eB k j ρ (Sum.inr a))) A33 b := by sorry





theorem rowP (x1 : U.RC k 1 (j + ρ)) (Q : B.Mat k (j + ρ)) (z : Fin (2 * (j + ρ) + k + 1)) :
    (G.wMat 1 * (Matrix.of x1.1)ᴴ * Hpk k (j + ρ) * Q) 0 z = Matrix.vecMul (star (c1v x1)) (Hpk k (j + ρ) * Q) z := by sorry




theorem star_column_components (x1 : U.RC k 1 (j + ρ)) :
    ((fun a => star (c1v x1) (U.eB k j ρ (Sum.inl (Sum.inl a)))) = star (cX x1)) ∧
    ((fun v => star (c1v x1) (U.eB k j ρ (Sum.inl (Sum.inr v)))) = star (cV x1)) ∧
    ((fun a => star (c1v x1) (U.eB k j ρ (Sum.inr a))) = star (cS x1)) := by sorry

theorem mul_unitriangular_castSucc_col {m : Type*} (x1 : U.RC k 1 (j + ρ)) (M : Matrix m (Fin (j + 1)) ℂ) (a : m) (b : Fin j) :
    (M * Ut0 x1) a b.castSucc = M a b.castSucc := by sorry







theorem mul_unitriangular_last_col {m : Type*} (x1 : U.RC k 1 (j + ρ)) (M : Matrix m (Fin (j + 1)) ℂ) (a : m) :
    (M * Ut0 x1) a (Fin.last j) = ∑ b : Fin j, M a b.castSucc * cS x1 b + M a (Fin.last j) := by sorry



theorem Cm_cs (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (v : Fin (2 * ρ + k + 1)) (b : Fin j) :
    (TX x1 x).1 v b.castSucc = x.1 v b := by sorry

theorem Cm_last (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (v : Fin (2 * ρ + k + 1)) :
    (TX x1 x).1 v (Fin.last j) = (cV x1 - Matrix.of x.1 *ᵥ cS x1) v := by sorry


theorem Z_cc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (a b : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) a.castSucc b.castSucc =
      ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + U.skewOf x.2) a b := by sorry


theorem Z_cl (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (a : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) a.castSucc (Fin.last j) =
      (-(1 / 2 : ℂ)) * (((Matrix.of x.1)ᴴ * Hpk k ρ) *ᵥ (cV x1 - Matrix.of x.1 *ᵥ cS x1)) a + nc x1 x a := by sorry





theorem Z_lc (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (b : Fin j) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) (Fin.last j) b.castSucc =
      (-(1 / 2 : ℂ)) * Matrix.vecMul (star (cV x1 - Matrix.of x.1 *ᵥ cS x1)) (Hpk k ρ * Matrix.of x.1) b -
        star (nc x1 x b) := by sorry








theorem Z_ll (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) :
    ((-(1 / 2 : ℂ)) • ((Matrix.of (TX x1 x).1)ᴴ * Hpk k ρ * Matrix.of (TX x1 x).1) + Sm x1 x) (Fin.last j) (Fin.last j) =
      (-(1 / 2 : ℂ)) * (star (cV x1 - Matrix.of x.1 *ᵥ cS x1) ⬝ᵥ (Hpk k ρ *ᵥ (cV x1 - Matrix.of x.1 *ᵥ cS x1))) +
        Complex.I * (q2L x1 x : ℂ) := by sorry







theorem dot_symm {n : Type*} [Fintype n] (H : Matrix n n ℂ) (u w : n → ℂ) :
    star (star w ⬝ᵥ (H *ᵥ u)) = star u ⬝ᵥ (Hᴴ *ᵥ w) := by sorry





theorem kl0 (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) (U.Rn k j ρ x)) =
      U.Rn k (j + 1) ρ (TX x1 x) * U.muP k (j + 1) ρ (Um x1) := by sorry











































































































































































































theorem castM_mul {a b : ℕ} (h : a = b) (A B' : B.Mat k a) : D.castM h (A * B') = D.castM h A * D.castM h B' := by sorry


theorem embG_mul {j' ρ' : ℕ} (A B' : B.Mat k ρ') : U.embG k j' ρ' (A * B') = U.embG k j' ρ' A * U.embG k j' ρ' B' := by sorry


theorem leviElement_mul {j' ρ' : ℕ} (q1 q2 : Matrix (Fin j') (Fin j') ℂ) :
    U.muP k j' ρ' q1 * U.muP k j' ρ' q2 = U.muP k j' ρ' (q1 * q2) := by sorry




def Dm (q : Matrix (Fin j) (Fin j) ℂ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ := sorry



theorem Dm_mul (q1 q2 : Matrix (Fin j) (Fin j) ℂ) : Dm q1 * Dm q2 = Dm (q1 * q2) := by sorry




theorem Dm_ct (q : Matrix (Fin j) (Fin j) ℂ) : (Dm q)ᴴ = Dm qᴴ := by sorry



theorem Dm_one : Dm (1 : Matrix (Fin j) (Fin j) ℂ) = 1 := by sorry




theorem Dm_inv (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) : (Dm q)⁻¹ = Dm q⁻¹ := by sorry



theorem emb_muP (q : Matrix (Fin j) (Fin j) ℂ) (hq : IsUnit q.det) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.embG k 1 (j + ρ) (U.muP k j ρ q)) = U.muP k (j + 1) ρ (Dm q) := by sorry


























theorem emb_emb (y : B.Mat k ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ) (U.embG k 1 (j + ρ) (U.embG k j ρ y)) = U.embG k (j + 1) ρ y := by sorry
























def TUU (x1 : U.RC k 1 (j + ρ)) (u : G.UT j → ℂ) : G.UT (j + 1) → ℂ := sorry


theorem dm_uni (q : Matrix (Fin j) (Fin j) ℂ) (hq : Ux2.uniK (Ux2.kU j) q) : Ux2.uniK (Ux2.kU (j + 1)) (Dm q) := by sorry












theorem upper_TUU (x1 : U.RC k 1 (j + ρ)) (u : G.UT j → ℂ) : G.upper (TUU x1 u) = Um x1 * Dm (G.upper u) := by sorry



theorem upper_det (u : G.UT j → ℂ) : IsUnit (G.upper u).det := by sorry

theorem kl (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (u : G.UT j → ℂ) (y : B.Mat k ρ) :
    D.castM (by omega : 1 + (j + ρ) = (j + 1) + ρ)
        (U.Rn k 1 (j + ρ) x1 * U.embG k 1 (j + ρ) (U.Rn k j ρ x * U.muP k j ρ (G.upper u) * U.embG k j ρ y)) =
      U.Rn k (j + 1) ρ (TX x1 x) * U.muP k (j + 1) ρ (G.upper (TUU x1 u)) * U.embG k (j + 1) ρ y := by sorry



end Formalism.FourierDecayAlt.P.Dx2.Split

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.SplitM

open Formalism.FourierDecayAlt.P.Dx2.Split

variable {k j ρ : ℕ}

theorem conj_mp : MeasurePreserving (fun z : ℂ => star z) volume volume := by sorry










theorem vconj_mp {ι : Type*} [Fintype ι] : MeasurePreserving (fun v : ι → ℂ => star v) volume volume := by sorry


theorem mp_vec {m : Type*} [Fintype m] [DecidableEq m] (g : Matrix m m ℂ) (h : ‖g.det‖ = 1) :
    MeasurePreserving (fun x : m → ℂ => g *ᵥ x) volume volume := by sorry










theorem norm_det_w (j : ℕ) : ‖(G.wMat j).det‖ = 1 := by sorry






theorem det_upper (u : G.UT j → ℂ) : (G.upper u).det = 1 := by sorry






theorem middle_four_swap_measure_preserving {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SigmaFinite μa] [SigmaFinite μb]
    [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by sorry










section fibre

variable (k j ρ)

abbrev Bs := sorry

abbrev Fs := sorry

variable {k j ρ}

def unipotentTranslateCoord (b : Bs k j ρ) (s : Fin j → ℂ) : Fin j → ℂ := sorry

def ncf (b : Bs k j ρ) (s : Fin j → ℂ) (v : Fin (2 * ρ + k + 1) → ℂ) (a : Fin j → ℂ) : Fin j → ℂ := sorry


def q2f (b : Bs k j ρ) (s : Fin j → ℂ) (v : Fin (2 * ρ + k + 1) → ℂ) (a : Fin j → ℂ) (t : ℝ) : ℝ := sorry



def lev1 (b : Bs k j ρ) (p : (Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) : (Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ) := sorry


def lev2 (b : Bs k j ρ) (p : ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ)) :
    ((Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) × (Fin j → ℂ) := sorry


def lev3 (b : Bs k j ρ) (p : Fs k j ρ) : Fs k j ρ := sorry

end fibre

theorem continuous_upper : Continuous (G.upper (d := j)) := by sorry




theorem continuous_skew : Continuous (U.skewOf (j := j)) := by sorry





theorem unipotent_coordinates_measure_preserving (b : Bs k j ρ) : MeasurePreserving (unipotentTranslateCoord b) volume volume := by sorry










theorem measurePreserving_first_level_map (b : Bs k j ρ) : MeasurePreserving (lev1 b) volume volume := by sorry





theorem measurePreserving_second_level_map (b : Bs k j ρ) : MeasurePreserving (lev2 b) volume volume := by sorry






theorem measurePreserving_third_level_map (b : Bs k j ρ) : MeasurePreserving (lev3 b) volume volume := by sorry





theorem tskew_mp : MeasurePreserving (fun p : Bs k j ρ × Fs k j ρ => (p.1, lev3 p.1 p.2)) volume volume := by sorry




















def swapIx : U.Ix k j ρ ≃ U.Ix k j ρ where
  toFun := sorry










def e1 (x1 : U.RC k 1 (j + ρ)) : Fs k j ρ := sorry

instance isEmpty_upperTriangular_one : IsEmpty (G.UT 1) := sorry




theorem measurePreserving_coord_equiv : MeasurePreserving (e1 (k := k) (j := j) (ρ := ρ)) volume volume := by sorry
































theorem src_mp : MeasurePreserving (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (z.2, e1 z.1)) volume volume := by sorry











def eL : G.UT j ⊕ Fin j ≃ G.UT (j + 1) where
  toFun := sorry



















def eZ : Fin j ⊕ G.UT j ≃ G.UT (j + 1) where
  toFun := sorry



















section combine

def rowE {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : Fin (j + 1) → α := sorry


theorem rowE_cs {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) (b : Fin j) : rowE p b.castSucc = p.1 b := by sorry


theorem rowE_last {α : Type*} [MeasurableSpace α] (p : (Fin j → α) × α) : rowE p (Fin.last j) = p.2 := by sorry


theorem rowE_mp {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (rowE (j := j) (α := α)) volume volume := by sorry






def combC (p : (Fin (2 * ρ + k + 1) → Fin j → ℂ) × (Fin (2 * ρ + k + 1) → ℂ)) :
    Fin (2 * ρ + k + 1) → Fin (j + 1) → ℂ := sorry

theorem combC_mp : MeasurePreserving (combC (k := k) (j := j) (ρ := ρ)) volume volume := by sorry






def combineUpperTriangularCoords (p : (G.UT j → ℂ) × (Fin j → ℂ)) : G.UT (j + 1) → ℂ := sorry


def combU (p : (Fin j → ℂ) × (G.UT j → ℂ)) : G.UT (j + 1) → ℂ := sorry


theorem combined_coordinates_measure_preserving : MeasurePreserving (combineUpperTriangularCoords (j := j)) volume volume := by sorry



theorem combU_mp : MeasurePreserving (combU (j := j)) volume volume := by sorry



theorem combined_coordinates_left (p : (G.UT j → ℂ) × (Fin j → ℂ)) (w : G.UT j) : combineUpperTriangularCoords p (eL (Sum.inl w)) = p.1 w := by sorry


theorem combineUpperTriangular_inr (p : (G.UT j → ℂ) × (Fin j → ℂ)) (a : Fin j) : combineUpperTriangularCoords p (eL (Sum.inr a)) = p.2 a := by sorry


theorem combU_inl (p : (Fin j → ℂ) × (G.UT j → ℂ)) (b : Fin j) : combU p (eZ (Sum.inl b)) = p.1 b := by sorry


theorem combU_inr (p : (Fin j → ℂ) × (G.UT j → ℂ)) (w : G.UT j) : combU p (eZ (Sum.inr w)) = p.2 w := by sorry


end combine

abbrev Ts := sorry


def perm8 (q : Bs k j ρ × Fs k j ρ) : Ts (k := k) (j := j) (ρ := ρ) := sorry


theorem measurePreserving_coord_permutation : MeasurePreserving (perm8 (k := k) (j := j) (ρ := ρ)) volume volume := by sorry




























def tgt (q : Bs k j ρ × Fs k j ρ) : U.RC k (j + 1) ρ × (G.UT (j + 1) → ℂ) := sorry


theorem tgt_mp : MeasurePreserving (tgt (k := k) (j := j) (ρ := ρ)) volume volume := by sorry





















theorem tgt_id (x1 : U.RC k 1 (j + ρ)) (x : U.RC k j ρ) (u : G.UT j → ℂ) :
    tgt ((x, u), lev3 (x, u) (e1 x1)) = (TX x1 x, TUU x1 u) := by sorry























































theorem T_mp : MeasurePreserving (fun z : U.RC k 1 (j + ρ) × Bs k j ρ => (TX z.1 z.2.1, TUU z.1 z.2.2))
    volume volume := by sorry







end Formalism.FourierDecayAlt.P.Dx2.SplitM

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.SplitF

open Formalism.FourierDecayAlt.P.Dx2.Split Formalism.FourierDecayAlt.P.Dx2.SplitM Formalism.FourierDecayAlt.P.Dx2.MN

variable {k : ℕ}

def Psi (k j ρ : ℕ) (z : U.RC k j ρ × ((G.UT j → ℂ) × Mt k ρ)) : Mt k (j + ρ) := sorry


theorem muN_cast {a b : ℕ} (h : a = b) : D.muN k b = (D.muN k a).map (castMt h) := by sorry




theorem castM_castM {a b c : ℕ} (h1 : a = b) (h2 : b = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by sorry


theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := by sorry

theorem block_three_zero_size_eq {ρ : ℕ} (A11 : Matrix (Fin 0) (Fin 0) ℂ) (A12 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin 0) (Fin 0) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin 0) ℂ) (A31 : Matrix (Fin 0) (Fin 0) ℂ)
    (A32 : Matrix (Fin 0) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin 0) (Fin 0) ℂ) :
    U.blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 = D.castM (by omega : ρ = 0 + ρ) A22 := by sorry







theorem psi_zero (ρ : ℕ) (z : U.RC k 0 ρ × ((G.UT 0 → ℂ) × Mt k ρ)) :
    Psi k 0 ρ z = castMt (by omega : ρ = 0 + ρ) z.2.2 := by sorry


theorem radial_measure_is_probability (ρ : ℕ) : IsProbabilityMeasure (U.muRC k 0 ρ) := by sorry














theorem split_zero (ρ : ℕ) :
    D.muN k (0 + ρ) = ((U.muRC k 0 ρ).prod ((volume : Measure (G.UT 0 → ℂ)).prod (D.muN k ρ))).map (Psi k 0 ρ) := by sorry












theorem continuous_block3_matrix {X : Type*} [TopologicalSpace X] {j ρ : ℕ}
    {f11 : X → Matrix (Fin j) (Fin j) ℂ} {f12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {f13 : X → Matrix (Fin j) (Fin j) ℂ} {f21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {f22 : X → B.Mat k ρ}
    {f23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {f31 : X → Matrix (Fin j) (Fin j) ℂ}
    {f32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {f33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : Continuous f11) (h12 : Continuous f12) (h13 : Continuous f13) (h21 : Continuous f21)
    (h22 : Continuous f22) (h23 : Continuous f23) (h31 : Continuous f31) (h32 : Continuous f32)
    (h33 : Continuous f33) :
    Continuous (fun x => U.blk3 (f11 x) (f12 x) (f13 x) (f21 x) (f22 x) (f23 x) (f31 x) (f32 x) (f33 x)) := by sorry












theorem rn_cont (j ρ : ℕ) : Continuous (fun x : U.RC k j ρ => U.Rn k j ρ x) := by sorry










theorem inv_upper_eq {j : ℕ} (u : G.UT j → ℂ) : (G.upper u)ᴴ⁻¹ = ((G.upper u)ᴴ).adjugate := by sorry


theorem mup_cont (j ρ : ℕ) : Continuous (fun u : G.UT j → ℂ => U.muP k j ρ (G.upper u)) := by sorry





theorem embg_cont (j ρ : ℕ) : Continuous (fun y : Mt k ρ => U.embG k j ρ (Matrix.of y)) := by sorry



theorem psi_cont (j ρ : ℕ) : Continuous (Psi k j ρ) := by sorry




theorem psi_meas (j ρ : ℕ) : Measurable (Psi k j ρ) := by sorry






theorem sf_RC (j' ρ' : ℕ) : SigmaFinite (U.muRC k j' ρ') := by sorry






def Phi (k j ρ : ℕ) (z : U.RC k 1 (j + ρ) × (U.RC k j ρ × ((G.UT j → ℂ) × Mt k ρ))) :
    U.RC k (j + 1) ρ × ((G.UT (j + 1) → ℂ) × Mt k ρ) := sorry


theorem phi_mp (j ρ : ℕ) [SigmaFinite (D.muN k ρ)] :
    MeasurePreserving (Phi k j ρ)
      ((U.muRC k 1 (j + ρ)).prod ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))))
      ((U.muRC k (j + 1) ρ).prod ((volume : Measure (G.UT (j + 1) → ℂ)).prod (D.muN k ρ))) := by sorry





















theorem split_succ (j : ℕ)
    (ih : ∀ ρ, D.muN k (j + ρ) =
      ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))).map (Psi k j ρ)) (ρ : ℕ) :
    D.muN k ((j + 1) + ρ) =
      ((U.muRC k (j + 1) ρ).prod ((volume : Measure (G.UT (j + 1) → ℂ)).prod (D.muN k ρ))).map (Psi k (j + 1) ρ) := by sorry




































theorem split_all : ∀ j ρ : ℕ, D.muN k (j + ρ) =
    ((U.muRC k j ρ).prod ((volume : Measure (G.UT j → ℂ)).prod (D.muN k ρ))).map (Psi k j ρ) := by sorry





end Formalism.FourierDecayAlt.P.Dx2.SplitF

namespace Formalism.FourierDecayAlt.P

theorem unipotent_measure_splitting : Formalism.FourierDecayAlt.D.MuNSplit := by sorry






end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Dx2.Rad

section pattern
variable {m : ℕ} (w : Equiv.Perm (Fin m))

def low (x : C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ := sorry

theorem low_apply (x : C2.Lstidx w → ℂ) (i j : Fin m) :
    low w x i j = (1 : Matrix (Fin m) (Fin m) ℂ) i j +
      if h : j < i ∧ w.symm i < w.symm j then x ⟨(i, j), h⟩ else 0 := by sorry


theorem low_coord (x : C2.Lstidx w → ℂ) (q : C2.Lstidx w) : low w x q.1.1 q.1.2 = x q := by sorry


variable (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
include hd

theorem low_mem (x : C2.Lstidx w → ℂ) : low w x ∈ C2.Lstg (C2.monoP w d) := by sorry


theorem eq_low {M : Matrix (Fin m) (Fin m) ℂ} (hM : M ∈ C2.Lstg (C2.monoP w d)) :
    M = low w (fun q => M q.1.1 q.1.2) := by sorry




theorem lstg_mul {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.Lstg (C2.monoP w d))
    (hB : B ∈ C2.Lstg (C2.monoP w d)) : A * B ∈ C2.Lstg (C2.monoP w d) := by sorry







end pattern

section posG
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem std : C2.Std k r D.z D.z' := by sorry

theorem isUnit_G {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) : IsUnit γ.det := by sorry


variable {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hpos : 0 < Gf k r D.z D.z' γ)
include hγ hpos

theorem rset_eq : C6.Rset γ = C2.Rst k r D.z D.z' γ := by sorry
















variable {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
include hd hZ

theorem u_lstg {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) : (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d) := by sorry









theorem exists_rho (x : C2.Lstidx w → ℂ) : ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ := by sorry












theorem u_inj : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ) := by sorry



end posG

structure Good {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) : Prop where
  ex : ∀ x : C2.Lstidx w → ℂ, ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ
  inj : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ)
  lst : ∀ ρ ∈ C6.Rset γ, (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d)

section meas
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hG : Good D γ w d)

def rhoF (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (x : C2.Lstidx w → ℂ) : B.Mat k r := sorry

include hγ hd hG

theorem rhoF_spec (x : C2.Lstidx w → ℂ) :
    rhoF D γ w x ∈ C6.Rset γ ∧ C2.uMap k r D.z (rhoF D γ w x) = (low w x)ᴴ := by sorry





theorem rhoF_unique (x : C2.Lstidx w → ℂ) {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ)
    (hu : C2.uMap k r D.z ρ = (low w x)ᴴ) : ρ = rhoF D γ w x := by sorry


omit hγ hd hG in

def phi0 (w : Equiv.Perm (Fin (r + 1))) (x : Mt k r) : C2.Lstidx w → ℂ := sorry


theorem u_eq_low {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) :
    (C2.uMap k r D.z ρ)ᴴ = low w (phi0 D w (Matrix.of.symm ρ)) := by sorry



theorem coordMap_hermRep_leftInverse (x : C2.Lstidx w → ℂ) : phi0 D w (Matrix.of.symm (rhoF D γ w x)) = x := by sorry






omit hγ hd hG in
theorem cont_uMap_entry (a b : Fin (r + 1)) : Continuous fun x : Mt k r => C2.uMap k r D.z (Matrix.of x) a b := by sorry






omit hγ hd hG in
theorem continuous_radial_phi : Continuous (phi0 D w : Mt k r → C2.Lstidx w → ℂ) := by sorry



theorem rhoF_meas : Measurable fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoF D γ w x) : Mt k r) := by sorry





















end meas

section shears
variable {m : ℕ} (w : Equiv.Perm (Fin m))

theorem sum_sub_single (f : Fin m → ℂ) (j : Fin m) (c : ℂ) :
    (∑ k, f k) - c = ∑ k, (f k - if k = j then c else 0) := by sorry


def rank (q : C2.Lstidx w) : ℕ := sorry

def Tl (L0 : Matrix (Fin m) (Fin m) ℂ) (x : C2.Lstidx w → ℂ) : C2.Lstidx w → ℂ := sorry


def Tr (L0 : Matrix (Fin m) (Fin m) ℂ) (x : C2.Lstidx w → ℂ) : C2.Lstidx w → ℂ := sorry


theorem cont_low : Continuous (low w) := by sorry











theorem Tl_mp (L0 : Matrix (Fin m) (Fin m) ℂ) (hL : L0 ∈ C2.LTset m) :
    MeasurePreserving (Tl w L0) volume volume := by sorry


























theorem Tr_mp (L0 : Matrix (Fin m) (Fin m) ℂ) (hL : L0 ∈ C2.LTset m) :
    MeasurePreserving (Tr w L0) volume volume := by sorry


























end shears

section haarPos
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem one_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by sorry


theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ Nset k r) : g ∈ Sset k r z := by sorry


theorem uMap_mul {a b : B.Mat k r} (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) :
    C2.uMap k r D.z (a * b) = C2.uMap k r D.z a * C2.uMap k r D.z b := by sorry


variable {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hG : Good D γ w d)
include hγ hd hG

theorem left_shift {a : B.Mat k r} (ha : a ∈ C6.Rset γ) (x : C2.Lstidx w → ℂ) :
    a * rhoF D γ w x = rhoF D γ w (Tl w (C2.uMap k r D.z a)ᴴ x) := by sorry








theorem right_shift {a : B.Mat k r} (ha : a ∈ C6.Rset γ) (x : C2.Lstidx w → ℂ) :
    rhoF D γ w x * a = rhoF D γ w (Tr w (C2.uMap k r D.z a)ᴴ x) := by sorry








theorem haar_good : B.IsHaarOn (C6.Rset γ) (Formalism.FourierDecayAlt.D.muR D γ w) := by sorry

















































end haarPos

section degen
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def yv (γ : B.Mat k r) (b : Fin r) : Fin (2 * r + k + 1) → ℂ := sorry

theorem fvec_cs (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) : fvec k r z b.castSucc = DF.ee k r b := by sorry


theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by sorry


include hZ in
theorem pz (a b : Fin (r + 1)) :
    herm (Hpk k r) (γ *ᵥ fvec k r D.z' b) (fvec k r D.z a) = if a = w b then d b else 0 := by sorry




include hB in
theorem w_cs (b : Fin r) : w b.castSucc ≠ Fin.last r := by sorry


include hB in
theorem w_cs' (b : Fin r) : (DF.piX w b).castSucc = w b.castSucc := by sorry

include hB in
theorem piX_bij : Function.Bijective (DF.piX w) := by sorry



def sX (hB : w (Fin.last r) = Fin.last r) : Equiv.Perm (Fin r) := sorry

theorem sX_apply (b : Fin r) : sX hB b = DF.piX w b := by sorry

include hZ hB in
theorem y_ee (a b : Fin r) : herm (Hpk k r) (yv γ b) (DF.ee k r a) = if a = sX hB b then d b.castSucc else 0 := by sorry





include hγ in
theorem y_y (b c : Fin r) : herm (Hpk k r) (yv γ b) (yv γ c) = 0 := by sorry


include hZ hB in
theorem y_z (b : Fin r) : herm (Hpk k r) (yv γ b) D.z = 0 := by sorry




end degen

section degen2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def uvD (γ : B.Mat k r) : Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => DF.ee k r a
  | Sum.inr b => yv γ b

def wvD (γ : B.Mat k r) (d : Fin (r + 1) → ℂ) (hB : w (Fin.last r) = Fin.last r) :
    Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl a => (d ((sX hB).symm a).castSucc)⁻¹ • yv γ ((sX hB).symm a)
  | Sum.inr b => (star (d b.castSucc))⁻¹ • DF.ee k r (sX hB b)

def YD (γ : B.Mat k r) (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Fin r ⊕ Fin r → Fin (2 * r + k + 1) → ℂ
  | Sum.inl b => ∑ a, u a.castSucc b.castSucc • DF.ee k r a
  | Sum.inr b => ∑ c, u' c.castSucc b.castSucc • yv γ c

include hγ hd hZ hB

theorem h1D (i j : Fin r ⊕ Fin r) :
    herm (Hpk k r) (uvD γ i) (wvD γ d hB j) = if i = j then 1 else 0 := by sorry














end degen2

section degen3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)
include hγ hd hZ hB

theorem h2D (x : Fin (2 * r + k + 1) → ℂ) (j : Fin r ⊕ Fin r) :
    herm (Hpk k r) x (uvD γ j) =
      ∑ i, herm (Hpk k r) x (wvD γ d hB i) * herm (Hpk k r) (uvD γ i) (uvD γ j) := by sorry





















theorem hermitian_radial_mixed_pair (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hrel : ∀ a b : Fin r, ∑ c, ∑ e, u' c.castSucc b.castSucc * star (u e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a)) (a b : Fin r) :
    herm (Hpk k r) (YD γ u u' (Sum.inr b)) (YD γ u u' (Sum.inl a)) = herm (Hpk k r) (yv γ b) (DF.ee k r a) := by sorry







theorem h3D (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hrel : ∀ a b : Fin r, ∑ c, ∑ e, u' c.castSucc b.castSucc * star (u e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a))
    (i j : Fin r ⊕ Fin r) :
    herm (Hpk k r) (YD γ u u' i) (YD γ u u' j) = herm (Hpk k r) (uvD γ i) (uvD γ j) := by sorry









omit hd hZ hB in
theorem h4D (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ j, herm (Hpk k r) x (uvD γ j) = 0) (i : Fin r ⊕ Fin r) : herm (Hpk k r) x (YD γ u u' i) = 0 := by sorry






end degen3

section degen4
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

def uP (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (x : C2.Lstidx w → ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := sorry

def rhoD (γ : B.Mat k r) (hB : w (Fin.last r) = Fin.last r) (d : Fin (r + 1) → ℂ) (x : C2.Lstidx w → ℂ) :
    B.Mat k r := sorry


include hd in
theorem upperUnipotent_mem_upperTriangular (x : C2.Lstidx w → ℂ) : uP w d x ∈ C2.UTset (r + 1) := by sorry






theorem low_last (x : C2.Lstidx w → ℂ) (a : Fin r) : low w x a.castSucc (Fin.last r) = 0 := by sorry



include hB in
theorem low_last' (x : C2.Lstidx w → ℂ) (a : Fin r) : low w x (Fin.last r) a.castSucc = 0 := by sorry






include hγ hd hZ hB

theorem hrelD (x : C2.Lstidx w → ℂ) (a b : Fin r) :
    ∑ c, ∑ e, uP w d x c.castSucc b.castSucc * star ((low w x)ᴴ e.castSucc a.castSucc) *
      herm (Hpk k r) (yv γ c) (DF.ee k r e) = herm (Hpk k r) (yv γ b) (DF.ee k r a) := by sorry






















theorem rhoD_UH (x : C2.Lstidx w → ℂ) : rhoD γ hB d x ∈ UH (Hpk k r) := by sorry



theorem rhoD_mulVec (x : C2.Lstidx w → ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rhoD γ hB d x *ᵥ v = v + ∑ i, herm (Hpk k r) v (wvD γ d hB i) •
      (YD γ (low w x)ᴴ (uP w d x) i - uvD γ i) := by sorry


theorem rhoD_u (x : C2.Lstidx w → ℂ) (i : Fin r ⊕ Fin r) :
    rhoD γ hB d x *ᵥ uvD γ i = YD γ (low w x)ᴴ (uP w d x) i := by sorry


theorem rhoD_fix (x : C2.Lstidx w → ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ i, herm (Hpk k r) v (wvD γ d hB i) = 0) : rhoD γ hB d x *ᵥ v = v := by sorry


end degen4

section degen5
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

omit D in
theorem entry (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : M i j = (M *ᵥ bvec j) i := by sorry


omit D in
theorem ee_apply_hi (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : DF.ee k r a i = 0 := by sorry



omit D in
theorem ee_sum_hi (t : Fin r → ℂ) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) :
    (∑ c, t c • DF.ee k r c) i = 0 := by sorry


omit D in
theorem ee_sum_lo (t : Fin r → ℂ) (c0 : Fin r) : (∑ c, t c • DF.ee k r c) (eI k r c0) = t c0 := by sorry



omit D in

theorem mem_N (M : B.Mat k r) (hM : M ∈ UH (Hpk k r)) (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hU : U ∈ C2.UTset (r + 1)) (he : ∀ a, M *ᵥ DF.ee k r a = ∑ c, U c.castSucc a.castSucc • DF.ee k r c)
    (hw : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (M *ᵥ bvec j) i = bvec j i) : M ∈ Nset k r := by sorry


















include hγ hd hZ hB

theorem herm_basis_isotropic_perp (b : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    herm (Hpk k r) (bvec j) (wvD γ d hB (Sum.inr b)) = 0 := by sorry










theorem rhoD_N (x : C2.Lstidx w → ℂ) : rhoD γ hB d x ∈ Nset k r := by sorry










theorem rhoD'_N (x : C2.Lstidx w → ℂ) : γ⁻¹ * rhoD γ hB d x * γ ∈ Nset k r := by sorry






























end degen5

section degen6
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)
include hγ hd hZ hB

theorem rhoD_alt (x : C2.Lstidx w → ℂ) : rhoD γ hB d x *ᵥ D.z = D.z := by sorry






theorem herm_zz_ne : herm (Hpk k r) D.z D.z ≠ 0 := by sorry






theorem uMap_rhoD (x : C2.Lstidx w → ℂ) : C2.uMap k r D.z (rhoD γ hB d x) = (low w x)ᴴ := by sorry






















theorem ex_degen (x : C2.Lstidx w → ℂ) : ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = (low w x)ᴴ := by sorry


end degen6

section gen
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)

theorem rel_uu' {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) (hγ : γ ∈ B.GV k r) :
    (C2.uMap k r D.z ρ)ᴴ * Zhat k r D.z D.z' γ * C2.uMap k r D.z' (γ⁻¹ * ρ * γ) = Zhat k r D.z D.z' γ := by sorry










include hγ hd hZ in
theorem lst_gen {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) : (C2.uMap k r D.z ρ)ᴴ ∈ C2.Lstg (C2.monoP w d) := by sorry









end gen

section degenInj
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
  {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
  {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
  (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) = Fin.last r)

omit D in
theorem pos_cases (i : Fin (2 * r + k + 1)) :
    (∃ c : Fin r, i = eI k r c) ∨ (r ≤ i.val ∧ i.val ≤ r + k) ∨ (∃ c : Fin r, i = esI k r c) := by sorry







omit D in
theorem decompX (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0) :
    v = ∑ c, v (eI k r c) • DF.ee k r c := by sorry






omit D in
theorem uMap_one (z : Fin (2 * r + k + 1) → ℂ) (hz : C2.StdZ k r z) : C2.uMap k r z (1 : B.Mat k r) = 1 := by sorry


include hγ hd hZ hB

theorem trivial_of_u_one {ρ : B.Mat k r} (hρ : ρ ∈ C6.Rset γ) (hu1 : C2.uMap k r D.z ρ = 1) : ρ = 1 := by sorry





































































































theorem inj_degen : Set.InjOn (C2.uMap k r D.z) (C6.Rset γ) := by sorry













end degenInj

section final
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)

theorem pos_of_w {γ : B.Mat k r} {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r D.z D.z' γ = C2.monoP w d) (hB : w (Fin.last r) ≠ Fin.last r) : 0 < Gf k r D.z D.z' γ := by sorry






















end final

theorem muRHaar : Formalism.FourierDecayAlt.D.MuRHaar := by sorry






end Formalism.FourierDecayAlt.P.Dx2.Rad

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.Dx2.VV

section law
variable {k r : ℕ}

def Tp (hA nA hB nB : B.Mat k r) (p : B.SS k r) : B.SS k r := sorry



def Tq (hA nA hB nB : B.Mat k r) (p : B.SS k r) : B.SS k r := sorry



theorem cont_Tp (hA nA hB nB : B.Mat k r) : Continuous (Tp hA nA hB nB) := by sorry









theorem cont_Tq (hA nA hB nB : B.Mat k r) : Continuous (Tq hA nA hB nB) := by sorry









variable {hA nA hB nB : B.Mat k r}

theorem Tq_Tp (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (p : B.SS k r) :
    Tq hA nA hB nB (Tp hA nA hB nB p) = p := by sorry











theorem Tp_Tq (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (p : B.SS k r) :
    Tp hA nA hB nB (Tq hA nA hB nB p) = p := by sorry











def Te (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) : B.SS k r ≃ᵐ B.SS k r where
  toFun := sorry






end law

section law2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem Tp_eq : Tp hA nA hB nB = Prod.map (Prod.map (lmulM hA) (conjM hA ∘ lmulM nA))
    (Prod.map (lmulM hB) (conjM hB ∘ lmulM nB)) := by sorry







theorem mp_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) :
    MeasurePreserving (Tp hA nA hB nB) S.μSS S.μSS := by sorry

















end law2

section alg
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem sgs_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (p : B.SS k r) (γ : B.Mat k r) :
    B.sgs (Tp hA nA hB nB p) γ = B.sgs p ((hA * nA)⁻¹ * γ * (hB * nB)) := by sorry




theorem act_Tp (uA : IsUnit hA.det) (vA : IsUnit nA.det) (uB : IsUnit hB.det) (vB : IsUnit nB.det) (γ : B.Mat k r)
    (uγ : IsUnit γ.det) (y : B.Mat k r) (p : B.SS k r) :
    Tp hA nA hB nB (C6.actR ((hA * nA)⁻¹ * γ * (hB * nB)) ((hA * nA)⁻¹ * y * (hA * nA)) p) =
      C6.actR γ y (Tp hA nA hB nB p) := by sorry






















theorem ell_fix {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : B.Mat k r}
    (hf : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) : ell k r z n = 0 := by sorry















theorem lam_Tp {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hf : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) (hx : x ∈ Nset k r) :
    B.lam k r z (h * n * x * h⁻¹) = B.lam k r z x := by sorry






end alg

section integrand
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem xiTau_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (p : B.SS k r) (h1 : Matrix.of p.1.2 ∈ Nset k r) (h2 : Matrix.of p.2.2 ∈ Nset k r) :
    B.xiTau S (1, 1) (Tp hA nA hB nB p) = B.xiTau S (1, 1) p := by sorry




def Cin (hA hB : B.Mat k r) (X : Wq →L[ℂ] Wp) : Wq →L[ℂ] Wp := sorry

theorem rho_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (hhA : hA ∈ UWset k r S.z) (hhB : hB ∈ UWset k r S.z')
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (p : B.SS k r)
    (h1 : Matrix.of p.1.1 ∈ UWset k r S.z) (h2 : Matrix.of p.2.1 ∈ UWset k r S.z') :
    B.rho S (Tp hA nA hB nB p) F γ = Cin S hA hB (B.rho S p F ((hA * nA)⁻¹ * γ * (hB * nB))) := by sorry







theorem integrand_Tp (uA : IsUnit hA.det) (uB : IsUnit hB.det) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (p : B.SS k r) (hp : S.inSS p) :
    Formalism.FourierDecayAlt.D.orbIntegrand S γ F (Tp hA nA hB nB p) = Cin S hA hB (Formalism.FourierDecayAlt.D.orbIntegrand S ((hA * nA)⁻¹ * γ * (hB * nB)) F p) := by sorry




end integrand

section lawMain
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

def conjA (hA nA : B.Mat k r) (x : Mt k r) : Mt k r := sorry

theorem cont_conjA (hA nA : B.Mat k r) : Continuous (conjA hA nA) := by sorry




theorem inSS_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {p : B.SS k r} (hp : S.inSS p) : S.inSS (Tp hA nA hB nB p) := by sorry









theorem inSS_Tq (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {p : B.SS k r} (hp : S.inSS p) : S.inSS (Tq hA nA hB nB p) := by sorry















theorem cut_Tp (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) {μR : Measure (Mt k r)} {θ : B.SS k r → ℝ}
    (hθ : Formalism.FourierDecayAlt.D.IsNormCut S γ μR θ) :
    Formalism.FourierDecayAlt.D.IsNormCut S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) (θ ∘ Tp hA nA hB nB) := by sorry














theorem cut_Tq (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) {μR : Measure (Mt k r)} {θ : B.SS k r → ℝ}
    (hθ : Formalism.FourierDecayAlt.D.IsNormCut S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) θ) :
    Formalism.FourierDecayAlt.D.IsNormCut S γ μR (θ ∘ Tq hA nA hB nB) := by sorry



















end lawMain

section lawFinal
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

def CinL (hA hB : B.Mat k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := sorry


theorem CinL_apply (hA hB : B.Mat k r) (X : Wq →L[ℂ] Wp) : CinL S hA hB X = Cin S hA hB X := by sorry

theorem CinL_inv (hhA : hA ∈ UWset k r S.z) (hhB : hB ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) :
    CinL S hA⁻¹ hB⁻¹ (CinL S hA hB X) = X := by sorry


















def IndepAt (γ : B.Mat k r) (μR : Measure (Mt k r)) : Prop := sorry






theorem orbJ_law (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (μR : Measure (Mt k r))
    (hInd : IndepAt S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA))) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    CinL S hA hB (Formalism.FourierDecayAlt.D.orbJ S ((hA * nA)⁻¹ * γ * (hB * nB)) (μR.map (conjA hA nA)) F) =
      Formalism.FourierDecayAlt.D.orbJ S γ μR F := by sorry





























































end lawFinal

section muRconj
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem conjN_in {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hx : x ∈ Nset k r) : (h * n)⁻¹ * x * (h * n) ∈ Nset k r := by sorry






theorem conjN_out {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h n x : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) (hx : x ∈ Nset k r) : (h * n) * x * (h * n)⁻¹ ∈ Nset k r := by sorry




theorem rset_conj (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r) (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (ρ : B.Mat k r) :
    ρ ∈ C6.Rset γ ↔ (hA * nA)⁻¹ * ρ * (hA * nA) ∈ C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB)) := by sorry


























theorem uMap_conj (hz : C2.StdZ k r S.z) {s ρ : B.Mat k r} (us : IsUnit s.det)
    (hs : ∀ b, s *ᵥ fvec k r S.z b = fvec k r S.z b) (hρ : ρ ∈ Nset k r) :
    C2.uMap k r S.z (s⁻¹ * ρ * s) = C2.uMap k r S.z ρ := by sorry















end muRconj

section muRconj2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)
variable {hA nA hB nB : B.Mat k r}

theorem rhoOfU_conj (hz : C2.StdZ k r S.z) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    (hsfix : ∀ b, (hA * nA) *ᵥ fvec k r S.z b = fvec k r S.z b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det)
    (hinj : Set.InjOn (C2.uMap k r S.z) (C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB))))
    (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Formalism.FourierDecayAlt.D.rhoOfU S ((hA * nA)⁻¹ * γ * (hB * nB)) u = (hA * nA)⁻¹ * Formalism.FourierDecayAlt.D.rhoOfU S γ u * (hA * nA) := by sorry

































theorem muR_conj (hz : C2.StdZ k r S.z) (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r)
    (hsfix : ∀ b, (hA * nA) *ᵥ fvec k r S.z b = fvec k r S.z b)
    {γ : B.Mat k r} (uγ : IsUnit γ.det) (w : Equiv.Perm (Fin (r + 1)))
    (hinj : Set.InjOn (C2.uMap k r S.z) (C6.Rset ((hA * nA)⁻¹ * γ * (hB * nB))))
    (hm : Measurable fun x : C2.Lstidx w → ℂ =>
      (Matrix.of.symm (Formalism.FourierDecayAlt.D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x))) : Mt k r)) :
    Formalism.FourierDecayAlt.D.muR S ((hA * nA)⁻¹ * γ * (hB * nB)) w = (Formalism.FourierDecayAlt.D.muR S γ w).map (conjA hA nA) := by sorry







end muRconj2

section atPoints
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem ptMatN_monoP' (p : C.LPt) (n : ℕ) (h : Formalism.FourierDecayAlt.D.ptSize p = n) (hb : ∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) :
    Formalism.FourierDecayAlt.D.ptMatN p n = C2.monoP (h ▸ Formalism.FourierDecayAlt.D.ptPerm p) (h ▸ Formalism.FourierDecayAlt.D.ptDiag p) ∧
      ∀ a, (h ▸ Formalism.FourierDecayAlt.D.ptDiag p) a ≠ 0 := by sorry



theorem uMap_fix {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r}
    (hs : ∀ b, s *ᵥ fvec k r z b = fvec k r z b) : C2.uMap k r z s = 1 := by sorry





theorem std_vector_z : C2.StdZ k r S.z := by sorry
theorem std_vector_z_prime : C2.StdZ k r S.z' := by sorry

theorem UW_fix {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) (b : Fin (r + 1)) :
    h *ᵥ fvec k r z b = fvec k r z b := by sorry





theorem mul_fix {z : Fin (2 * r + k + 1) → ℂ} {h n : B.Mat k r} (hh : h ∈ UWset k r z)
    (hn : ∀ b, n *ᵥ fvec k r z b = fvec k r z b) (b : Fin (r + 1)) :
    (h * n) *ᵥ fvec k r z b = fvec k r z b := by sorry


theorem zhat_conj {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (γ : B.Mat k r) : Zhat k r S.z S.z' ((hA * nA)⁻¹ * γ * (hB * nB)) = Zhat k r S.z S.z' γ := by sorry




theorem mem_GV_conj {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) :
    (hA * nA)⁻¹ * γ * (hB * nB) ∈ B.GV k r := by sorry



theorem gf_eq {γ γ' : B.Mat k r} (h : Zhat k r S.z S.z' γ = Zhat k r S.z S.z' γ') :
    Gf k r S.z S.z' γ = Gf k r S.z S.z' γ' := by sorry


theorem orbJ_pt (p : C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1)) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    (hZ : Zhat k r S.z S.z' γ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1)) (hpos : 0 < Gf k r S.z S.z' γ)
    {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    CinL S hA hB (Formalism.FourierDecayAlt.D.orbJ S ((hA * nA)⁻¹ * γ * (hB * nB))
        (Formalism.FourierDecayAlt.D.muR S ((hA * nA)⁻¹ * γ * (hB * nB)) (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F) =
      Formalism.FourierDecayAlt.D.orbJ S γ (Formalism.FourierDecayAlt.D.muR S γ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F := by sorry






















end atPoints

section explicit
open Formalism.FourierDecayAlt.P.Dx2.DF

theorem smat_comm_Hpk {k r : ℕ} {ι : Type*} [Fintype ι] (u w Y : ι → Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hg : g ∈ UH (Hpk k r)) (hu : ∀ i, g *ᵥ u i = u i) (hw : ∀ i, g *ᵥ w i = w i) (hY : ∀ i, g *ᵥ Y i = Y i) :
    smat (Hpk k r) u w Y * g = g * smat (Hpk k r) u w Y := by sorry













end explicit

section explicit2
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ}

theorem caseA' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (a0 b0 : Fin r) (ha : π (Fin.last r) = a0.castSucc)
    (hb : π b0.castSucc = Fin.last r) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by sorry





























































































































































































































theorem caseB' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by sorry
































































































































































































































end explicit2

section frameHelpers
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ}

theorem Wb_N {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : Wb (n *ᵥ v) = Wb v := by sorry






















theorem prW_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : D.prW k r z (n *ᵥ v) = D.prW k r z v := by sorry


theorem free_of_fix {h : B.Mat k r} (hU : h ∈ UH (Hpk k r)) (hme : ∀ a : Fin r, h *ᵥ ee k r a = ee k r a)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (a : Fin r) : (h *ᵥ v) (esI k r a) = 0 := by sorry


theorem uw_parts {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) :
    h ∈ UH (Hpk k r) ∧ (∀ a : Fin r, h *ᵥ ee k r a = ee k r a) ∧ (∀ a : Fin r, h *ᵥ es k r a = es k r a) ∧
      h *ᵥ z = z := by sorry


theorem prW_sinv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0)
    {h n : B.Mat k r} (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : D.prW k r z ((h * n)⁻¹ *ᵥ v) = h⁻¹ *ᵥ D.prW k r z v := by sorry




theorem unit_c {x y : Fin (2 * r + k + 1) → ℂ} (hx : herm (Hpk k r) x x = 1) (c : ℝ) (hc : 0 < c)
    (hy : herm (Hpk k r) y y = 1) (h : y = (c : ℂ) • x) : y = x := by sorry







end frameHelpers

section cof
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem cofR_conj {sA sB γ : B.Mat k r} (hfB : ∀ b, sB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (hZ1 : Zhat k r S.z S.z' (sA⁻¹ * γ * sB) = Zhat k r S.z S.z' γ) :
    Formalism.FourierDecayAlt.D.cofR S (sA⁻¹ * γ * sB) = sA⁻¹ *ᵥ Formalism.FourierDecayAlt.D.cofR S γ := by sorry





theorem cofL_eq {γ1 γ : B.Mat k r} (hZ1 : Zhat k r S.z S.z' γ1 = Zhat k r S.z S.z' γ) :
    Formalism.FourierDecayAlt.D.cofL S γ1 = Formalism.FourierDecayAlt.D.cofL S γ := by sorry


theorem cofR_free (γ : B.Mat k r) (a : Fin r) : Formalism.FourierDecayAlt.D.cofR S γ (esI k r a) = 0 := by sorry












theorem cofL_free {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (a : Fin r) :
    (γ⁻¹ *ᵥ Formalism.FourierDecayAlt.D.cofL S γ) (esI k r a) = 0 := by sorry





















end cof

section frameFix
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem ext_basis {z' ν' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hν : inWb k r ν')
    (hzz : herm (Hpk k r) z' z' ≠ 0) (hνz : herm (Hpk k r) ν' z' = 0) (hνν : herm (Hpk k r) ν' ν' = 1)
    {M N : B.Mat k r} (he : ∀ a, M *ᵥ ee k r a = N *ᵥ ee k r a) (hs : ∀ a, M *ᵥ es k r a = N *ᵥ es k r a)
    (hz : M *ᵥ z' = N *ᵥ z') (hn : M *ᵥ ν' = N *ᵥ ν')
    (hw : ∀ w, inWb k r w → herm (Hpk k r) w z' = 0 → herm (Hpk k r) w ν' = 0 → M *ᵥ w = N *ᵥ w) : M = N := by sorry





















theorem frame_fix (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀)
    {σ : B.Mat k r} (hσU : σ ∈ UH (Hpk k r))
    (hE3 : ∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x)
    (hE2 : ∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ)
    (hγe : m₀ * σ ∈ B.GV k r) (hDe : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ))
    (hdet : (Zhat k r S.z S.z' (m₀ * σ)).det ≠ 0)
    {hA nA hB nB : B.Mat k r} (hhA : hA ∈ UWset k r S.z) (hnA : nA ∈ Nset k r)
    (hfA : ∀ b, nA *ᵥ fvec k r S.z b = fvec k r S.z b)
    (hhB : hB ∈ UWset k r S.z') (hnB : nB ∈ Nset k r) (hfB : ∀ b, nB *ᵥ fvec k r S.z' b = fvec k r S.z' b)
    (hD1 : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ ((hA * nA)⁻¹ * (m₀ * σ) * (hB * nB))) :
    hA⁻¹ * (m₀ * σ) * hB = m₀ * σ := by sorry
















































































































end frameFix

section final
open Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq)

theorem exE (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (p : C.LPt)
    (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1)) (hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz k r S.z * Tz k r S.z') r p) :
    ∃ σ : B.Mat k r, m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ) := by sorry






















theorem stabilizer_decomp_unitary_mul_unipotent {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r} (hs : s ∈ C2.CurvatureSupportSet k r z) :
    ∃ h ∈ UWset k r z, ∃ n ∈ Nset k r, (∀ b, n *ᵥ fvec k r z b = fvec k r z b) ∧ s = h * n := by sorry













theorem orbJ_rep (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1))
    (hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz k r S.z * Tz k r S.z') r p) {σ : B.Mat k r}
    (hE : m₀ * σ ∈ B.GV k r ∧ Zhat k r S.z S.z' (m₀ * σ) = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (m₀ * σ) ∧ σ ∈ UH (Hpk k r) ∧
      (∀ x, inWb k r x → herm (Hpk k r) x S.z' = 0 → herm (Hpk k r) x ν' = 0 → σ *ᵥ x = x) ∧
      (∀ g ∈ UH (Hpk k r), (∀ a : Fin r, g *ᵥ ee k r a = ee k r a ∧ g *ᵥ es k r a = es k r a) →
        g *ᵥ S.z' = S.z' → g *ᵥ ν' = ν' → σ * g = g * σ))
    {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hZ : Zhat k r S.z S.z' γ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1))
    (hD : Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ γ) :
    Formalism.FourierDecayAlt.D.orbJ S γ (Formalism.FourierDecayAlt.D.muR S γ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F =
      Formalism.FourierDecayAlt.D.orbJ S (m₀ * σ) (Formalism.FourierDecayAlt.D.muR S (m₀ * σ) (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F := by sorry


















end final

end Formalism.FourierDecayAlt.P.Dx2.VV

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Dx2.VV in
theorem isotropic_vectors_linear_indep : Formalism.FourierDecayAlt.D.VecVIndep := by sorry









end Formalism.FourierDecayAlt.P

end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.Dx2.SL

theorem curry_mp (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by sorry













variable {ph n : ℕ}

def sigP (σ : Equiv.Perm (Fin ph)) : Equiv.Perm (Fin (ph + (n + 1))) := sorry


theorem blockPerm_castAdd (σ : Equiv.Perm (Fin ph)) (i : Fin ph) :
    sigP (n := n) σ (Fin.castAdd (n + 1) i) = Fin.castAdd (n + 1) (σ i) := by sorry


theorem blockPerm_natAdd (σ : Equiv.Perm (Fin ph)) (i : Fin (n + 1)) :
    sigP σ (Fin.natAdd ph i) = Fin.natAdd ph (Fin.rev i) := by sorry


theorem blockPerm_symm_castAdd (σ : Equiv.Perm (Fin ph)) (i : Fin ph) :
    (sigP (n := n) σ).symm (Fin.castAdd (n + 1) i) = Fin.castAdd (n + 1) (σ.symm i) := by sorry


theorem blockPerm_symm_natAdd (σ : Equiv.Perm (Fin ph)) (i : Fin (n + 1)) :
    (sigP σ).symm (Fin.natAdd ph i) = Fin.natAdd ph (Fin.rev i) := by sorry


def dP (d : Fin ph → ℂ) (t : ℂ) : Fin (ph + (n + 1)) → ℂ := sorry

def lwIn (σ : Equiv.Perm (Fin ph)) : U.LW σ ⊕ (Fin (n + 1) × Fin ph) → U.LW (sigP (n := n) σ)
  | Sum.inl q => ⟨(Fin.castAdd (n + 1) q.1.1, Fin.castAdd (n + 1) q.1.2), by
      refine ⟨q.2.1, ?_⟩
      show (sigP (n := n) σ).symm (Fin.castAdd (n + 1) q.1.2) < (sigP σ).symm (Fin.castAdd (n + 1) q.1.1)
      rw [blockPerm_symm_castAdd, blockPerm_symm_castAdd]; exact q.2.2⟩
  | Sum.inr (i, j) => ⟨(Fin.natAdd ph i, Fin.castAdd (n + 1) j), by
      refine ⟨show j.val < ph + i.val by omega, ?_⟩
      show (sigP (n := n) σ).symm (Fin.castAdd (n + 1) j) < (sigP σ).symm (Fin.natAdd ph i)
      rw [blockPerm_symm_castAdd, blockPerm_symm_natAdd]
      show (σ.symm j).val < ph + (Fin.rev i).val
      have := (σ.symm j).isLt; omega⟩

theorem lwIn_bij (σ : Equiv.Perm (Fin ph)) : Function.Bijective (lwIn (n := n) σ) := by sorry




























def lwEquiv (σ : Equiv.Perm (Fin ph)) : U.LW (sigP (n := n) σ) ≃ U.LW σ ⊕ (Fin (n + 1) × Fin ph) := sorry


def utIn : (G.UT ph ⊕ (Fin ph × Fin (n + 1))) ⊕ G.UT (n + 1) → G.UT (ph + (n + 1))
  | Sum.inl (Sum.inl q) => ⟨(Fin.castAdd (n + 1) q.1.1, Fin.castAdd (n + 1) q.1.2), by
      exact q.2⟩
  | Sum.inl (Sum.inr (i, j)) => ⟨(Fin.castAdd (n + 1) i, Fin.natAdd ph j), show i.val < ph + j.val by omega⟩
  | Sum.inr q => ⟨(Fin.natAdd ph q.1.1, Fin.natAdd ph q.1.2), show ph + q.1.1.val < ph + q.1.2.val by
      have : q.1.1.val < q.1.2.val := q.2; omega⟩

theorem utIn_bij : Function.Bijective (utIn (ph := ph) (n := n)) := by sorry






















def utEquiv : G.UT (ph + (n + 1)) ≃ (G.UT ph ⊕ (Fin ph × Fin (n + 1))) ⊕ G.UT (n + 1) := sorry


section blocks
variable {p s : ℕ}

theorem b_cc (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin p) : U.blk2 A B C D (Fin.castAdd s i) (Fin.castAdd s j) = A i j := by sorry

theorem b_cn (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin p) (j : Fin s) : U.blk2 A B C D (Fin.castAdd s i) (Fin.natAdd p j) = B i j := by sorry

theorem b_nc (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) (j : Fin p) : U.blk2 A B C D (Fin.natAdd p i) (Fin.castAdd s j) = C i j := by sorry

theorem b_nn (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) : U.blk2 A B C D (Fin.natAdd p i) (Fin.natAdd p j) = D i j := by sorry


theorem one_cn (i : Fin p) (j : Fin s) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.castAdd s i) (Fin.natAdd p j) = 0 := by sorry

theorem one_nc (i : Fin s) (j : Fin p) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.natAdd p i) (Fin.castAdd s j) = 0 := by sorry

theorem one_cc (i j : Fin p) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.castAdd s i) (Fin.castAdd s j) =
    (1 : Matrix (Fin p) (Fin p) ℂ) i j := by sorry

theorem one_nn (i j : Fin s) : (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) (Fin.natAdd p i) (Fin.natAdd p j) =
    (1 : Matrix (Fin s) (Fin s) ℂ) i j := by sorry


end blocks

theorem permutationMatrix_extend_eq_fromBlocks (σ : Equiv.Perm (Fin ph)) : U.wP (sigP (n := n) σ) = U.blk2 (U.wP σ) 0 0 (G.wMat (n + 1)) := by sorry















theorem diag_dP (d : Fin ph → ℂ) (t : ℂ) :
    Matrix.diagonal (dP (n := n) d t) = U.blk2 (Matrix.diagonal d) 0 0 (t • 1) := by sorry













theorem lowW_sigP (σ : Equiv.Perm (Fin ph)) (v : U.LW (sigP (n := n) σ) → ℂ) :
    U.lowW (sigP σ) v = U.blk2 (U.lowW σ (fun q => v (lwIn σ (Sum.inl q)))) 0
      (Matrix.of fun i j => v (lwIn σ (Sum.inr (i, j)))) 1 := by sorry











































theorem upper_split (u : G.UT (ph + (n + 1)) → ℂ) :
    G.upper u = U.blk2 (G.upper (fun q => u (utIn (Sum.inl (Sum.inl q)))))
      (Matrix.of fun i j => u (utIn (Sum.inl (Sum.inr (i, j))))) 0 (G.upper (fun q => u (utIn (Sum.inr q)))) := by sorry

























section ident
variable (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)

def v1 (v : U.LW (sigP (n := n) σ) → ℂ) : U.LW σ → ℂ := sorry
def Am (v : U.LW (sigP (n := n) σ) → ℂ) : Matrix (Fin (n + 1)) (Fin ph) ℂ := sorry
def u1 (u : G.UT (ph + (n + 1)) → ℂ) : G.UT ph → ℂ := sorry
def Bm (u : G.UT (ph + (n + 1)) → ℂ) : Matrix (Fin ph) (Fin (n + 1)) ℂ := sorry
def u2 (u : G.UT (ph + (n + 1)) → ℂ) : G.UT (n + 1) → ℂ := sorry

def aN (v : U.LW (sigP (n := n) σ) → ℂ) : Matrix (Fin (n + 1)) (Fin ph) ℂ := sorry

def bN (u : G.UT (ph + (n + 1)) → ℂ) : Matrix (Fin ph) (Fin (n + 1)) ℂ := sorry

theorem headH_split (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.headH (sigP σ) (dP d t) v u =
      U.blk2 (U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * G.upper (u1 u))
        (U.wP σ * U.lowW σ (v1 σ v) * Matrix.diagonal d * Bm u)
        (G.wMat (n + 1) * Am σ v * Matrix.diagonal d * G.upper (u1 u))
        (G.wMat (n + 1) * Am σ v * Matrix.diagonal d * Bm u + t • (G.wMat (n + 1) * G.upper (u2 u))) := by sorry






theorem isUnit_low (v : U.LW σ → ℂ) : IsUnit (U.lowW σ v).det := by sorry
theorem isUnit_up {m : ℕ} (u : G.UT m → ℂ) : IsUnit (G.upper u).det := by sorry
theorem isUnit_wP {m : ℕ} (τ : Equiv.Perm (Fin m)) : IsUnit (U.wP τ).det := by sorry


theorem zj_zero {P : ℕ} (a : Fin 0 → Fin P → ℂ) (b : Fin P → Fin 0 → ℂ) (H : Matrix (Fin P) (Fin P) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : U.Zj a b H Z = H := by sorry







theorem zj_split (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.headH (sigP σ) (dP d t) v u =
      U.Zj (Matrix.of.symm (aN σ v)) (Matrix.of.symm (bN u)) (U.headH σ d (v1 σ v) (u1 u))
        (t • G.wMat (n + 1) * G.upper (u2 u)) := by sorry

















end ident

section chars
variable (σ : Equiv.Perm (Fin ph))

theorem blockPerm_symm₂ : (sigP (n := n) σ).symm = sigP σ.symm := by sorry





theorem psi_add (β x y : ℂ) : G.psi β (x + y) = G.psi β x * G.psi β y := by sorry




theorem subS_one {m : ℕ} : U.subS (1 : Matrix (Fin m) (Fin m) ℂ) = 0 := by sorry






theorem supS_superSum {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : U.supS M = G.superSum M := by sorry






theorem cornerA_zero {P : ℕ} (a : Fin 0 → Fin P → ℂ) : U.cornerA a = 0 := by sorry
theorem cornerB_zero {P : ℕ} (b : Fin P → Fin 0 → ℂ) : U.cornerB b = 0 := by sorry

theorem conj_split (v : U.LW (sigP (n := n) σ) → ℂ) :
    U.wP (sigP σ) * U.lowW (sigP σ) v * (U.wP (sigP σ))⁻¹ =
      U.blk2 1 0 (Matrix.of (Matrix.of.symm (aN σ v))) 1 *
        U.blk2 (U.wP σ * U.lowW σ (v1 σ v) * (U.wP σ)⁻¹) 0 0 1 := by sorry












theorem upper_fact (u : G.UT (ph + (n + 1)) → ℂ) :
    G.upper u = U.blk2 (G.upper (u1 u)) 0 0 (G.upper (u2 u)) * U.blk2 1 (Matrix.of (Matrix.of.symm (bN u))) 0 1 := by sorry







theorem psiH_split (β : ℂ) (a0 : Fin 0 → Fin (ph + (n + 1)) → ℂ) (b0 : Fin (ph + (n + 1)) → Fin 0 → ℂ)
    (v : U.LW (sigP (n := n) σ) → ℂ) (u : G.UT (ph + (n + 1)) → ℂ) :
    U.psiH (s := 0) β (sigP σ) ((a0, b0), (v, u)) =
      U.psiH (s := n + 1) β σ ((Matrix.of.symm (aN σ v), Matrix.of.symm (bN u)), (v1 σ v, u1 u)) *
        G.psi β (G.superSum (G.upper (u2 u))) := by sorry















end chars

section meas

theorem reindex_mp {ι κ X : Type} [Fintype ι] [Fintype κ] [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (e : ι ≃ κ) : MeasurePreserving (fun (y : κ → X) (i : ι) => y (e i)) volume volume := by sorry












theorem row_mp {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun x : Fin m → ℂ => Matrix.vecMul x N) volume volume := by sorry












end meas

section shear

theorem permutationMatrix_eq_permMatrix'' {m : ℕ} (τ : Equiv.Perm (Fin m)) : U.wP τ = τ.permMatrix ℂ := by sorry



theorem normSq_det_wP {m : ℕ} (τ : Equiv.Perm (Fin m)) : Complex.normSq (U.wP τ).det = 1 := by sorry



theorem det_inv_low (σ : Equiv.Perm (Fin ph)) (v : U.LW σ → ℂ) : ((U.lowW σ v)⁻¹).det = 1 := by sorry

theorem det_inv_up {m : ℕ} (u : G.UT m → ℂ) : ((G.upper u)⁻¹).det = 1 := by sorry


theorem fa_mp (N : Matrix (Fin ph) (Fin ph) ℂ) (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun y : Fin (n + 1) → Fin ph → ℂ => Matrix.of.symm (G.wMat (n + 1) * Matrix.of y * N))
      volume volume := by sorry













theorem swap_mp (a b : ℕ) :
    MeasurePreserving (fun (y : Fin a → Fin b → ℂ) (j : Fin b) (i : Fin a) => y i j) volume volume := by sorry









theorem fb_mp (M : Matrix (Fin ph) (Fin ph) ℂ) (hM : Complex.normSq M.det = 1) :
    MeasurePreserving (fun y : Fin ph → Fin (n + 1) → ℂ => Matrix.of.symm (M * Matrix.of y)) volume volume := by sorry














end shear

section chain

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem assoc_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ) ((μa.prod μb).prod μc)
      (μa.prod (μb.prod μc)) := by sorry


def swap4 : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) := sorry




theorem measurePreserving_prod_middle_swap (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa] [SFinite μb]
    [SFinite μc] [SFinite μd] :
    MeasurePreserving (swap4 : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ)) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by sorry
















def dropE (T Y : Type) [MeasurableSpace T] [MeasurableSpace Y] [Unique T] : T × Y ≃ᵐ Y where
  toFun p := sorry






theorem dropE_mp (T Y : Type) [MeasurableSpace T] [MeasurableSpace Y] [Unique T] (μ : Measure T)
    [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν] : MeasurePreserving (dropE T Y) (μ.prod ν) ν := by sorry


def reE {ι κ X : Type} [MeasurableSpace X] (e : ι ≃ κ) : (κ → X) ≃ᵐ (ι → X) where
  toFun y i := sorry






end chain

section shearE
variable (σ : Equiv.Perm (Fin ph))

theorem cont_lowW : Continuous (U.lowW σ) := by sorry








theorem cont_upper {m : ℕ} : Continuous (G.upper (d := m)) := by sorry








theorem inv_adj {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (h : A.det = 1) : A⁻¹ = A.adjugate := by sorry


def shF (x : (U.LW σ → ℂ) × (G.UT ph → ℂ)) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) :
    (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ) := sorry



def shG (x : (U.LW σ → ℂ) × (G.UT ph → ℂ)) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) :
    (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ) := sorry



theorem shG_shF (x) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) : shG σ x (shF σ x y) = y := by sorry












theorem shF_shG (x) (y : (Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) : shF σ x (shG σ x y) = y := by sorry












theorem cont_shF : Continuous (fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
    ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => shF σ p.1 p.2) := by sorry















theorem cont_shG : Continuous (fun p : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) ×
    ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) => shG σ p.1 p.2) := by sorry








def shearE : ((U.LW σ → ℂ) × (G.UT ph → ℂ)) × ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) ≃ᵐ
    ((U.LW σ → ℂ) × (G.UT ph → ℂ)) × ((Fin (n + 1) → Fin ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) where
  toFun p := sorry






theorem shearE_mp : MeasurePreserving (shearE (n := n) σ) volume volume := by sorry

















end shearE

section split
variable (σ : Equiv.Perm (Fin ph))

def lwSplit : (U.LW (sigP (n := n) σ) → ℂ) ≃ᵐ (U.LW σ → ℂ) × (Fin (n + 1) → Fin ph → ℂ) := sorry



theorem lwSplit_mp : MeasurePreserving (lwSplit (n := n) σ) volume (volume.prod volume) := by sorry









def utSplit : (G.UT (ph + (n + 1)) → ℂ) ≃ᵐ ((G.UT ph → ℂ) × (Fin ph → Fin (n + 1) → ℂ)) × (G.UT (n + 1) → ℂ) := sorry





theorem utSplit_mp : MeasurePreserving (utSplit (ph := ph) (n := n)) volume
    ((volume.prod volume).prod volume) := by sorry













end split

section xi
variable (σ : Equiv.Perm (Fin ph))

instance isProbabilityMeasure_pi_fin_zero {X : Type} [MeasureSpace X] : IsProbabilityMeasure (volume : Measure (Fin 0 → X)) := sorry


instance uniqueT (P : ℕ) : Unique ((Fin 0 → Fin P → ℂ) × (Fin P → Fin 0 → ℂ)) where
  default := sorry


theorem probT (P : ℕ) : IsProbabilityMeasure (volume : Measure ((Fin 0 → Fin P → ℂ) × (Fin P → Fin 0 → ℂ))) := by sorry




def xiE : U.XiH (ph + (n + 1)) 0 (sigP σ) ≃ᵐ U.XiH ph (n + 1) σ × (G.UT (n + 1) → ℂ) := sorry






theorem xiE_apply (η : U.XiH (ph + (n + 1)) 0 (sigP σ)) :
    xiE σ η = (((Matrix.of.symm (aN σ η.2.1), Matrix.of.symm (bN η.2.2)), (v1 σ η.2.1, u1 η.2.2)), u2 η.2.2) := by sorry




theorem xiE_mp : MeasurePreserving (xiE (n := n) σ) volume (volume.prod volume) := by sorry






















end xi

section core

theorem card_UT (m : ℕ) : 2 * Fintype.card (G.UT m) = m * (m - 1) := by sorry

















theorem card_UT' (n : ℕ) : Fintype.card (G.UT (n + 1)) = (n + 1) * n / 2 := by sorry




theorem pi_const_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by sorry







theorem norm_betaU : ‖U.betaU‖ = 2 := by sorry


theorem muPi_betaU (ι : Type) [Fintype ι] :
    G.muPi U.betaU ι = (Real.toNNReal (1 / Real.pi) ^ Fintype.card ι) • (volume : Measure (ι → ℂ)) := by sorry



end core

section main

theorem sigma_RC (k j ρ : ℕ) : SigmaFinite (U.muRC k j ρ) := by sorry








variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem core (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ)
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (n + 1) + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (sigP σ) =>
        U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) z z' ξ • F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + (n + 1)) 0 ρ (sigP σ))) :
    U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (sigP σ) (dP d t) z z' F (fun a => a.elim0) γ =
      ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t := by sorry





















































































end main

section wrap

theorem ptSize_cons (b : ℕ × ℂ) (h : C.LPt) : D.ptSize (b :: h) = b.1 + D.ptSize h := by sorry


theorem ptSize_append (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by sorry


theorem partner_append (s : ℕ) (t : ℂ) : ∀ (h : C.LPt) (a : ℕ), a < D.ptSize h + s →
    D.ptPartner (h ++ [(s, t)]) a = if a < D.ptSize h then D.ptPartner h a else D.ptSize h + (s - 1 - (a - D.ptSize h))
  | [], a, ha => by
    simp only [List.nil_append, D.ptPartner, D.ptSize, List.map_nil, List.sum_nil] at ha ⊢
    rw [if_pos (by omega)]; simp
  | b :: h, a, ha => by
    rw [ptSize_cons] at ha
    simp only [List.cons_append, D.ptPartner, ptSize_cons]
    by_cases h1 : a < b.1
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, partner_append s t h (a - b.1) (by omega)]
      by_cases h2 : a - b.1 < D.ptSize h
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega)]; omega

theorem scal_append (s : ℕ) (t : ℂ) : ∀ (h : C.LPt) (a : ℕ), a < D.ptSize h + s →
    D.ptScal (h ++ [(s, t)]) a = if a < D.ptSize h then D.ptScal h a else t
  | [], a, ha => by
    simp only [List.nil_append, D.ptScal, D.ptSize, List.map_nil, List.sum_nil] at ha ⊢
    rw [if_pos (by omega)]; simp
  | b :: h, a, ha => by
    rw [ptSize_cons] at ha
    simp only [List.cons_append, D.ptScal, ptSize_cons]
    by_cases h1 : a < b.1
    · rw [if_pos h1, if_pos (by omega), if_pos h1]
    · rw [if_neg h1, scal_append s t h (a - b.1) (by omega)]
      by_cases h2 : a - b.1 < D.ptSize h
      · rw [if_pos h2, if_pos (by omega), if_neg h1]
      · rw [if_neg h2, if_neg (by omega)]

theorem isLocPt_head {h : C.LPt} {s : ℕ} {t : ℂ} (hl : D.IsLocPt (h ++ [(s, t)]) (D.ptSize (h ++ [(s, t)]))) :
    D.IsLocPt h (D.ptSize h) := by sorry


theorem phi_transport {k ρ P P' : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : P = P')
    (σ : Equiv.Perm (Fin P)) (σ' : Equiv.Perm (Fin P')) (hσ : ∀ a : Fin P, (σ' (Fin.cast e a)).val = (σ a).val)
    (dd : Fin P → ℂ) (dd' : Fin P' → ℂ) (hd : ∀ a : Fin P, dd' (Fin.cast e a) = dd a)
    (z z' : Fin (2 * (P + 0 + ρ) + k + 1) → ℂ) (F : B.Mat k (P + 0 + ρ) → E) (γ : B.Mat k ρ) :
    (Integrable (fun ξ : U.Xi k P 0 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ dd ξ (fun a => a.elim0) γ))
        (U.muXi k P 0 ρ σ) →
      Integrable (fun ξ : U.Xi k P' 0 ρ σ' => U.psiStar k ρ σ' (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k ρ σ' dd' ξ (fun a => a.elim0) γ)) (U.muXi k P' 0 ρ σ')) ∧
    U.PhiFun k ρ σ dd z z' F (fun a => a.elim0) γ =
      U.PhiFun k ρ σ' dd' (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) (fun a => a.elim0) γ := by sorry













end wrap

section final

theorem castV_castV {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by sorry


theorem castF_castF {k a b c : ℕ} {E : Type} (h1 : a = b) (h2 : b = c) (F : B.Mat k c → E) :
    D.castF h1 (D.castF h2 F) = D.castF (h1.trans h2) F := by sorry


theorem sliceOm : D.SliceOm := by sorry








































end final

end Formalism.FourierDecayAlt.P.Dx2.SL

end

namespace Formalism.FourierDecayAlt.P

theorem nilpotent_measure_is_haar : Formalism.FourierDecayAlt.D.MuNHaar := by sorry

theorem unipotent_dual_lattice_covolume : Formalism.FourierDecayAlt.D.NhatCovol := by sorry

theorem exists_level_tower : Formalism.FourierDecayAlt.D.TowerExists := by sorry

theorem exists_isotropic_frame : Formalism.FourierDecayAlt.D.DFrameExists := by sorry

theorem radial_measure_is_haar : Formalism.FourierDecayAlt.D.MuRHaar := by sorry

theorem slice_measure_identity : Formalism.FourierDecayAlt.D.SliceOm := by sorry

end Formalism.FourierDecayAlt.P
