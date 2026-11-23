module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicityStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite


open GlobalTheory.PolFan.MultBound in
theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTopStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.max_multiplicity_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | exact GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOne

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal

theorem smoothEnd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ :=
  fun _ _ _ _ _ _ _ _ _ _ hD hPF hSL hM => GlobalTheory.PolFan.SmoothEnd.isPolFan_of_maxMult_le_one hD hPF hSL hM

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOneStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.smooth_of_max_multiplicity_le_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd | exact GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFan

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.FanResolution

theorem resolution : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ := by
  intro O _ _ _ _ bar w0 hO q φ lab hDom
  suffices key : ∀ (n : ℕ) (φ lab : InvFun O), maxMult bar q φ = n → IsPolyFan bar q φ →
      IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab →
      ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ by
    intro hP hT hL hS
    have hfin := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ hP
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult bar q φ
    · have hfin : maxMult bar q φ < ⊤ := by
        rw [hn]
        exact ENat.natCast_lt_top n
      obtain ⟨φ', lab', hP', hT', hL', hS', hSub, hlt⟩ :=
        GlobalTheory.T.exists_fan_lower_max_multiplicity O bar w0 hO q φ lab hDom hP hT hL hS hfin h2
      have hfin' := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ' hP'
      obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp hfin'.ne
      have hlt' : n' < n := by
        rw [hn, ← hn'] at hlt
        exact_mod_cast hlt
      obtain ⟨φ'', g1, g2, g3, g4⟩ := ih n' hlt' φ' lab' hn'.symm hP' hT' hL' hS'
      exact ⟨φ'', g1, g2, g3, fun χ hχ => g4 χ (hSub χ hχ)⟩
    · have hle : maxMult bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have h3 : ¬ (2 ≤ n) := by exact_mod_cast h2
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨g1, g2⟩ := GlobalTheory.T.smooth_of_max_multiplicity_le_one O bar hO q φ lab hDom hP hS hle
      exact ⟨φ, g1, g2, hT, fun χ hχ => hχ⟩

end GlobalTheory.CompanionTheory.Ar.Fan.FanResolution
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_smooth_subordinate_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution | exact GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution <;> assumption)
end
end
