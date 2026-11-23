module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.AbsComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.CentComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.FinPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HaarComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.NormEx
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotFubini
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotMass
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotPos
public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Untwist

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbComm

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbComm :
    UpperTheory.V.Z.Tf.Orb.TwOrbComm → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbComm := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ f f' p1 p2 p3 p4
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a f f' p1 p2 p3 p4 fun x => by rw [h1]
  simpa only [c] using t
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.OrbLin

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.orbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbLin → UpperTheory.V.Z.Tf.Orb.Untwist → UpperTheory.V.Z.Tf.Orb.OrbLin := by
  intro hT hU k _ _ _ _ _ n _ _ μk hμk γ hγ μ hμ
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := hU k n μk γ
  obtain ⟨μ', a, b, c⟩ := h3 μ hμ
  have t := hT k k 1 h0 n μk hμk γ (h2 hγ) μ' a
  simpa only [c] using t
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotRight

section

@[expose] public section

open MeasureTheory PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.V.Z.Tf.Orb.quotRight :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotRight := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG hR H μ hs hinv F hF hFH y
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H μ (fun g => ρ (g * y)) := by
      refine ⟨hρ.1.comp (measurable_mul_const y), fun g => ?_⟩
      simpa only [mul_assoc] using hρ.2 (g * y)
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H μ hs hinv (fun g => F (g * y)) (hF.comp (measurable_mul_const y))
        (fun h hh g => by rw [mul_assoc, hFH h hh]) _ hρ']
    exact integral_mul_right_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · simp only [quotIntegral, dif_neg hex]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCent

section

@[expose] public section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc

theorem UpperTheory.V.Z.Tf.Orb.twCent :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent := by
  intro hE hG hC k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ _ n δ hδ
  have := (hG E n).2.2.1
  have hc := ((hE k E).2.2 n).2 σ
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨isClosed_eq (f := fun g : GL (Fin n) E => g⁻¹ * δ * sigmaGL σ g) ((continuous_inv.mul continuous_const).mul hc)
    continuous_const, fun a ha b hb => ?_⟩
  have h1 := congrArg Units.val (twCent_commute_twNorm _ hp δ ha)
  have h2 := congrArg Units.val (twCent_commute_twNorm _ hp δ hb)
  exact Units.ext (hC E n _ a.val b.val hδ h1 h2)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbComm

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbComm :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.Unimod → UpperTheory.V.Z.Tf.Orb.AbsComm → UpperTheory.V.Z.Tf.Orb.TwOrbComm := by
  intro hG hX hC hP hH hU hA k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ a b a1 a2 b1 b2 ha
  obtain ⟨g1, g2, g3, -, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, -⟩ := hH _ _ c1 c2 μ hμ
  obtain ⟨u1, u2⟩ := hU E n μE hμE
  have hs := ((hX k E).2.2 n).2 σ
  have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hp : ∀ (m : ℕ) x, a (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) x) = a x := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', ha, ih]
  have t := hA _ μE hμE u1 u2 (sigmaGL σ) hs _ Module.finrank_pos.ne' hl δ (hP k E σ hσ n δ hδ) μ hμ i2 a b a1 a2 b1 b2
  simpa only [hp] using t
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbFin

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbFin :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.NormEx → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotPos → UpperTheory.V.Z.Tf.Orb.TwOrbFin := by
  intro hG hX hC hP hH hN hI hQ k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE φ hφ hc δ hδ μ hμ
  obtain ⟨g1, g2, g3, g4, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, i3⟩ := hH _ _ c1 c2 μ hμ
  have hs := ((hX k E).2.2 n).2 σ
  obtain ⟨ρ, hρ, -⟩ := hN _ g4 _ c1 μ hμ i3
  have hF : Continuous fun g => φ (twConj (sigmaGL σ) g δ) := hφ.comp ((continuous_inv.mul continuous_const).mul hs)
  have hinv : ∀ h ∈ twCent (sigmaGL σ) δ, ∀ g, φ (twConj (sigmaGL σ) (h * g) δ) = φ (twConj (sigmaGL σ) g δ) :=
    fun h hh g => by rw [twConj_mul_left _ _ hh]
  have hM : CptMod (twCent (sigmaGL σ) δ) fun g => φ (twConj (sigmaGL σ) g δ) := by
    obtain ⟨D, hD, h⟩ := hP k E σ hσ n δ hδ _ hc
    exact ⟨D, hD, fun g hg => h g (subset_tsupport _ hg)⟩
  exact ⟨⟨ρ, hρ⟩, hI _ μE hμE _ c1 μ hμ i2 _ hF hinv hM,
    fun p q => hQ _ μE hμE _ c1 μ hμ i2 ⟨ρ, hρ⟩ _ hF hinv hM (fun g => p _) q⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbLin

section

@[expose] public section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbFin → UpperTheory.V.Z.Tf.Orb.TwOrbLin := by
  intro hT k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ
  refine ⟨fun c φ => ?_, fun φ ψ a1 a2 b1 b2 => ?_⟩
  · simp only [twOrbIntegralC, quotIntegral]
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    · simp
  · obtain ⟨h, p, -⟩ := hT k E σ hσ n μE hμE φ a1 a2 δ hδ μ hμ
    obtain ⟨-, q, -⟩ := hT k E σ hσ n μE hμE ψ b1 b2 δ hδ μ hμ
    simp only [twOrbIntegralC, quotIntegral, dif_pos h, Pi.add_apply, add_mul]
    exact integral_add (p _ h.choose_spec) (q _ h.choose_spec)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf

section

@[expose] public section

namespace UpperTheory.V.Z.Tf.Orb

theorem gLTop_of : GLTop := gLTop

theorem extCont_of : ExtCont := extCont

theorem centComm_of : CentComm := centComm

theorem twCent_of : TwCent := twCent extCont_of gLTop_of centComm_of

theorem unimod_of : Unimod := unimod gLTop_of

theorem finPres_of : FinPres := finPres

theorem haarComm_of : HaarComm := haarComm

theorem quotIndep_of : QuotIndep := quotIndep

theorem normEx_of : NormEx := normEx

theorem quotMass_of : QuotMass := quotMass

theorem quotInt_of : QuotInt := quotInt quotMass_of

theorem quotPos_of : QuotPos := quotPos quotIndep_of quotInt_of quotMass_of

theorem quotRight_of : QuotRight := quotRight quotIndep_of

theorem quotFubini_of : QuotFubini := quotFubini quotMass_of

theorem absComm_of : AbsComm := absComm quotFubini_of quotRight_of finPres_of

theorem untwist_of : Untwist := untwist

theorem twOrbFin_of (h : OrbProper) : TwOrbFin := twOrbFin gLTop_of extCont_of twCent_of h haarComm_of normEx_of quotInt_of quotPos_of

theorem twOrbLin_of (h : OrbProper) : TwOrbLin := twOrbLin (twOrbFin_of h)

theorem orbLin_of (h : OrbProper) : OrbLin := orbLin (twOrbLin_of h) untwist_of

theorem twOrbComm_of (h : OrbProper) : TwOrbComm := twOrbComm gLTop_of extCont_of twCent_of h haarComm_of unimod_of absComm_of

theorem orbComm_of (h : OrbProper) : OrbComm := orbComm (twOrbComm_of h) untwist_of

end UpperTheory.V.Z.Tf.Orb
end
end
