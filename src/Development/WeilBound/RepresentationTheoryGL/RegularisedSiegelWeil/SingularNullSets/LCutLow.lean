module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowB

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

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) (γ : hermA D n)
    (hγ : γ ∈ ratHerm D n) (x : hermA D n) : chn ψ β (γ + x) = chn ψ β x := by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem per_nb {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n)
    (γ : hermA D n) (hγ : γ ∈ ratHerm D n) (x : hermA D n) : F (nb (γ + x) * g) = F (nb x * g) := by
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

theorem pch_rat (ψ : AddChar (AF D.host.F) ℂ) (x : Mx D n n) (β : HermE D n) :
    pch ψ x (rat β.1) = ψ (GlobalTheory.CompanionTheory.FourierN.pr β.1 x) := by
  show ψ (halfTr (Matrix.trace (x * β.1.map (incA D)))) = ψ (halfTr (Matrix.trace (β.1.map (incA D) * x)))
  rw [Matrix.trace_mul_comm]

theorem fc_eq (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam := rfl

theorem chn_shift (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b x : hermA D n) :
    chn ψ β b = chn ψ β (b + x) * pch ψ x.1 (rat β.1) := by
  rw [chn_eq, chn_eq, pch_rat, ← AddChar.map_add_eq_mul]
  congr 1
  rw [show (b + x).1 = b.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right]
  abel


theorem fc_nb_mul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) (β : HermE D n) (x : hermA D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β (nb x * g) = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  have hper : ∀ γ ∈ ratHerm D n, ∀ b, F (nb (γ + b) * g) * chn ψ β (γ + b) = F (nb b * g) * chn ψ β b := fun γ hγ b => by
    rw [per_nb hinv hnb g γ hγ b, chn_per hψ β γ hγ b]
  have h : ∫ b in 𝓖, F (nb (b + x) * g) * chn ψ β (b + x) ∂lam = ∫ b in 𝓖, F (nb b * g) * chn ψ β b ∂lam :=
    GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D n) lam hFD (fun b => F (nb b * g) * chn ψ β b) hper x
  rw [fc_eq, fc_eq, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * (nb x * g)) * chn ψ β b = pch ψ x.1 (rat β.1) * (F (nb (b + x) * g) * chn ψ β (b + x))
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc, chn_shift ψ β b x]
  ring


theorem integrableOn_fc {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) (β : HermE D n) (h : G D n) :
    IntegrableOn (fun b => F (nb b * h) * chn ψ β b) 𝓖 lam := by
  obtain ⟨hnb, hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  have : BorelSpace (Mx D n n) := ⟨rfl⟩
  have : BorelSpace (hermA D n) := Subtype.borelSpace _
  have : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (hermA D n) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : DiscreteTopology (ratHerm D n) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  have : Countable (ratHerm D n) := countable_of_Lindelof_of_discrete
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PcFc.exists_bound_of_periodic (ratHerm D n) hK hcov _ (cont_nb hF hnb h)
    (per_nb hinv hnb h)
  refine Measure.integrableOn_of_bounded (M := M) (by rw [h1]; exact ENNReal.one_ne_top)
    ((cont_nb hF hnb h).mul (chn_cont hψ β)).aestronglyMeasurable (.of_forall fun b => ?_)
  rw [norm_mul, show ‖chn ψ β b‖ = 1 from hψ.2.1 _, mul_one]
  exact hM b

theorem fc_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (β : HermE D n)
    {x : hermA D n} (hx : IntAt v x) {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb F β g = pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  rw [← fc_nb_mul hψ hC hinv β x g, fc_eq, fc_eq]
  refine integral_congr_ae (.of_forall fun b => ?_)
  show F (nb b * g) * _ = F (nb b * (nb x * g)) * _
  rw [commute_of_atPts (nb_mem_atPts hC.1 v hx.1 hx.2.1) hg, ← mul_assoc, hK _ (nb_mem_KAt hC.1 v hx) _]

theorem fc_cutR {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (C : Cut D n v) (β : HermE D n) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) :
    fc ψ lam 𝓖 nb (cutR nb C F) β g = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
  have e : ∀ b, cutR nb C F (nb b * g) * chn ψ β b =
      ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) := fun b => by
    unfold cutR
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc (nb b) g, ← commute_of_atPts (nb_mem_atPts hC.1 v (C.inf x hx) (C.off x hx)) hg, mul_assoc]
  calc fc ψ lam 𝓖 nb (cutR nb C F) β g
      = ∫ b in 𝓖, ∑ x ∈ C.s, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_congr_ae (.of_forall e)
    _ = ∑ x ∈ C.s, ∫ b in 𝓖, C.co x * (F (nb b * (nb x * g)) * chn ψ β b) ∂lam :=
        integral_finsetSum _ fun x _ => (integrableOn_fc hψ hC hF hinv β (nb x * g)).const_mul _
    _ = ∑ x ∈ C.s, C.co x * fc ψ lam 𝓖 nb F β (nb x * g) :=
        Finset.sum_congr rfl fun x _ => integral_const_mul _ _
    _ = ∑ x ∈ C.s, C.co x * (pch ψ x.1 (rat β.1) * fc ψ lam 𝓖 nb F β g) :=
        Finset.sum_congr rfl fun x _ => by rw [fc_nb_mul hψ hC hinv]
    _ = cutF ψ C (rat β.1) * fc ψ lam 𝓖 nb F β g := by
        rw [cutF, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

end PositivityTheory.Rg.Rsw.L.LCutLow

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLow

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

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
end
end
