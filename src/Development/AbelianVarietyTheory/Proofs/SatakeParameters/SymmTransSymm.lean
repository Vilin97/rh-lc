module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponents
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeAtBadPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFramesStatement
public import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponentsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameAgree.frame_away | exact GlobalTheory.FrameAgree.frame_away | (intros; apply GlobalTheory.FrameAgree.frame_away <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFramesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TopFrameQ.topDat_frames_tie | exact GlobalTheory.TopFrameQ.topDat_frames_tie | (intros; apply GlobalTheory.TopFrameQ.topDat_frames_tie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOnStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | exact GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | (intros; apply GlobalTheory.TwV.AwayTopG.topDat_frames_vGs <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelowStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.point_decoration_agree_below : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  first | exact @GlobalTheory.TwV.AwayLat.lat_eq | exact GlobalTheory.TwV.AwayLat.lat_eq | (intros; apply GlobalTheory.TwV.AwayLat.lat_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCouplingCosetInvariantFrameCongruentOne

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetLoc

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem intAt_qOf_pow (P : HeightOneSpectrum (𝓞 E)) (t : ℕ) : IntAt P ((qOf P : E) ^ t) := by
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ t)

theorem congr_of_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (D a k : ℕ) (hak : a + k ≤ D)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (g z - z) ∈ stdAt E n P)
    (y0 x : Sp E n) (hy : ∀ l, IntAt P ((qOf P : E) ^ a * y0 l))
    (hx : ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (x - y0) l)) :
    ∀ l, IntAt P (((qOf P : E) ^ k)⁻¹ * (g x - y0) l) := by
  have hc : (qOf P : E) ≠ 0 := qOf_ne_zero P
  have hxa : ∀ l, IntAt P ((qOf P : E) ^ a * x l) := fun l => by
    have e : (qOf P : E) ^ a * x l = (qOf P : E) ^ a * y0 l + (qOf P : E) ^ (a + k) * (((qOf P : E) ^ k)⁻¹ * (x - y0) l) := by
      simp only [Pi.sub_apply]
      rw [pow_add]
      field_simp
      ring
    rw [e]
    exact (hy l).add ((intAt_qOf_pow P _).mul (hx l))
  have hz : (qOf P : E) ^ a • x ∈ stdAt E n P := (mem_localization_standardLattice P _).2 fun l => by simpa using hxa l
  have h1 := (mem_localization_standardLattice P _).1 (hg _ hz)
  obtain ⟨t, ht⟩ : ∃ t, D = t + (a + k) := ⟨D - (a + k), by omega⟩
  intro l
  have e : ((qOf P : E) ^ k)⁻¹ * (g x - y0) l = ((qOf P : E) ^ k)⁻¹ * (x - y0) l +
      (qOf P : E) ^ t * ((((qOf P : E) ^ D)⁻¹ • (g ((qOf P : E) ^ a • x) - (qOf P : E) ^ a • x)) l) := by
    rw [map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ht]
    simp only [pow_add]
    field_simp
    ring
  rw [e]
  exact (hx l).add ((intAt_qOf_pow P t).mul (h1 l))

theorem symm_sub_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (κ : Sp E n ≃ₗ[E] Sp E n) (D : ℕ) (hk : κ ∈ GLint E n P)
    (hg : ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ z - z) ∈ stdAt E n P) :
    ∀ z ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) ∈ stdAt E n P := by
  intro z hz
  have hk' : ∀ x, κ x ∈ stdAt E n P ↔ x ∈ stdAt E n P := hk
  have hz' : κ.symm z ∈ stdAt E n P := (hk' _).1 (by simpa using hz)
  have h := hg _ hz'
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm z - z) = -(((qOf P : E) ^ D)⁻¹ • (z - κ.symm z)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact (stdAt E n P).neg_mem h

end Local

end GlobalTheory.CosetLoc

namespace GlobalTheory.CosetLoc


open Classical in
theorem sameCoset_symm_iff : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  intro X Pr sel S mu cst P n κ y0 hc hk hg hD hy1 hy2 w
  have hg' := symm_sub_one κ (cst.D P) hk hg

  obtain ⟨a, hak, hy⟩ : ∃ a, a + (if P.1 ∈ Pr.vGs then 0 else cst.M) ≤ cst.D P ∧ ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ a * y0 l) := by
    by_cases hP : P.1 ∈ Pr.vGs
    · refine ⟨1, ?_, fun l => by simpa using hy1 hP l⟩
      rw [if_pos hP]
      simpa using hc.D_pos P
    · refine ⟨cst.M, ?_, hy2 hP⟩
      rw [if_neg hP]
      have := hD hP
      omega
  unfold SameCoset
  constructor
  · intro h
    have := congr_of_sub_one κ (cst.D P) a _ hak hg y0 (κ.symm w) hy h
    simpa using this
  · intro h
    exact congr_of_sub_one κ.symm (cst.D P) a _ hak hg' y0 w hy h

end GlobalTheory.CosetLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCouplingCosetInvariantFrameCongruentOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  first | exact @GlobalTheory.CosetLoc.sameCoset_symm_iff | exact GlobalTheory.CosetLoc.sameCoset_symm_iff | (intros; apply GlobalTheory.CosetLoc.sameCoset_symm_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTop

theorem inFr_trans {E : Type} [Field E] {n m : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (g g₁ : Sp E m ≃ₗ[E] Sp E m) (z : HomE E n m) :
    inFr f₁ g₁ z = (g₁.trans g.symm).symm.toLinearMap ∘ₗ inFr f g z ∘ₗ (f₁.trans f.symm).toLinearMap := by
  refine LinearMap.ext fun w => ?_
  simp [inFr, LinearEquiv.trans_symm]

theorem symm_trans_symm {E : Type} [Field E] {n : ℕ} (f f₁ : Sp E n ≃ₗ[E] Sp E n) (y : Sp E n) :
    f₁.symm y = (f₁.trans f.symm).symm (f.symm y) := by
  simp [LinearEquiv.trans_symm]

theorem ptAway_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 + 1 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi hi1
  subst hi1
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  have hagS : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 :=
    fun v hv => (hag v hv).1
  have hagT : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun v hv => (hag v hv).2
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have e : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' =
      XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' := by
    intro q q'
    funext z
    unfold xiPt
    rw [dite_eq_right (by omega), if_neg (by omega)]
  rw [e, e]

  have hF := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS
  have hF' := GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT

  have hcos : cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁ = cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p := by
    ext y
    simp only [cosetOf, Set.mem_setOf_eq]
    refine forall_congr' fun P => ?_
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      ((GlobalTheory.TwU.Model.sameCoset_equiv t.sel (t.tup μ) (t.cst μ) P).refl _)
    have key := GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm)
      (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) hc (hF P).1 (hF P).2 (hok.depthQ P) hb.1 hb.2 ((frsF t.sel (t.tup μ) p P).symm y)
    rw [← symm_trans_symm] at key
    exact key
  rw [hcos]
  funext z
  rw [XiTop_eq, XiTop_eq]
  congr 1
  ·
    unfold phiT
    congr 1
    refine propext (forall_congr' fun P => ?_)
    have hA := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hA' := GlobalTheory.T.point_decoration_agree_below A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    have hB := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ p p₁ h1 h3 hagS P
    have hB' := GlobalTheory.T.chartFunctional_eq_of_agree_at_badPlaces A dtU a hP hTie (t.m2 + 1 + 1) hi β' x' x₁' p' p₁' h2 h4 hagT P
    rw [hA, hA']
    refine forall_congr' fun w => imp_congr_right fun hw => and_congr_right fun hzw => ?_
    rw [hB w hw (hA ▸ hw), hB' _ hzw (hA' ▸ hzw)]
  ·
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p) (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
    have hrep : repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) ⟨r, hr⟩
    have hb := GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie (Nat.le_of_succ_le hi) β P _ (hrep P)
    rw [inFr_trans (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P) (frsF t.sel (t.tup μ) p' P) (frsF t.sel (t.tup μ) p₁' P) z,
      symm_trans_symm (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p₁ P)]
    by_cases hG : P.1 ∈ t.Pr.vGs
    · exact GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.1 hG)
    · exact GlobalTheory.T.lastStepDatum_twistPrime_invariant_congruentFrames A dtU a hP hTie P hG _ _ (hF P).1 (hF P).2 (hF' P).1 (hF' P).2 _ _ (hb.2 hG)

end GlobalTheory.TwV.AwayTop

end
end
end
