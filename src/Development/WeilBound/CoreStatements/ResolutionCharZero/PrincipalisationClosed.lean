module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlowupOfAgreeingIdealCartierStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierRestrictIffCartierAt
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupCompStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.VanishingIdealSmoothAgreesOffStatement
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupport

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_notMem_support {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupportStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierRestrictIffCartierAtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.effCartier_restrict_iff_cartier_at : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupportStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem _root_.GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.BlowupIntegral

theorem dense_compl_support_of_effCartier {Y : Scheme.{0}} [IsReduced Y] (I : Y.IdealSheafData)
    (hI : FinalTheorems.EffCartier I) : Dense ((I.support.compl : Y.Opens) : Set Y) := by
  rw [dense_iff_inter_open]
  rintro W hW ⟨x, hx⟩
  by_contra hc
  obtain ⟨U, f, hxU, hf, hIU⟩ := hI x
  obtain ⟨t, ht, hxt⟩ := U.2.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨x, hx⟩ hxU
  have h0 : f * t = 0 := by
    rw [← basicOpen_eq_bot_iff, Scheme.basicOpen_mul, eq_bot_iff]
    rintro y ⟨hyf, hyt⟩
    refine hc ⟨y, ht hyt, fun hy' => ?_⟩
    have hyU : y ∈ U.1 := Y.basicOpen_le f hyf
    have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
    rw [Scheme.mem_zeroLocus_iff] at this
    exact this f (by rw [hIU]; exact Ideal.subset_span rfl) hyf
  have ht0 : t = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff hf).1 h0
  subst ht0
  simp at hxt

theorem isIntegral_of_blowup {X₁ X₂ : Scheme.{0}} (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁) [IsIntegral X₁]
    [IsReduced X₂] [Nonempty X₂] (hb : FinalTheorems.Blowup π Z) : IsIntegral X₂ := by
  let V : X₁.Opens := Z.support.compl
  have hbV : IsIso (π ∣_ V) := GlobalTheory.Principalise.isIso_restrict_of_blowup hb V fun _ hx => hx
  have hU : (Z.comap π).support.compl = π ⁻¹ᵁ V := by
    ext y
    exact not_congr (GlobalTheory.ProjBlowup.mem_support_comap Z π y)
  have hd : Dense ((π ⁻¹ᵁ V : X₂.Opens) : Set X₂) := hU ▸ dense_compl_support_of_effCartier _ hb.1
  have hne : Nonempty (π ⁻¹ᵁ V).toScheme := hd.nonempty.to_subtype
  have : Nonempty V.toScheme := ⟨(π ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral (π ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (π ∣_ V)
  have h := ((IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ V).toScheme).image _
    (π ⁻¹ᵁ V).ι.continuous.continuousOn).closure
  rw [Set.image_univ, Scheme.Opens.range_ι, hd.closure_eq] at h
  have : IrreducibleSpace X₂ := (irreducibleSpace_def _).2 h
  exact isIntegral_of_irreducibleSpace_of_isReduced X₂

theorem isIntegral_of_smooth_blowup : ∀ {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k)
    (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁), IsIntegral X₁ → FinalTheorems.Blowup π Z → Smooth (π ≫ g) → Nonempty X₂ →
      IsIntegral X₂ := by
  intro k _ X₁ X₂ g Z π h₁ hb hs h₂
  have : IsReduced X₂ := GlobalTheory.isReduced_of_smooth_of_isReduced (π ≫ g)
  exact isIntegral_of_blowup Z π hb

end GlobalTheory.CompanionTheory.BlowupIntegral
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmoothStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.isIntegral_blowup_of_smooth : ∀ {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁), IsIntegral X₁ → FinalTheorems.Blowup π Z → Smooth (π ≫ g) → Nonempty X₂ → IsIntegral X₂ := by
  first | exact @GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | exact GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | (intros; apply GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrincipalisationOfCharZero

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

open GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.Resolution

theorem exists_centre_off {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁)
    (V : X₁.Opens) (h₀ : Smooth g) (h₁ : IsIntegral X₁) (h₂ : Smooth (Z.subschemeι ≫ g)) (h₃ : FinalTheorems.Blowup π Z)
    (h₄ : IsIso (π ∣_ V)) :
    ∃ Z' : X₁.IdealSheafData, Smooth (Z'.subschemeι ≫ g) ∧ (Z'.support : Set X₁) ⊆ (V : Set X₁)ᶜ ∧
      FinalTheorems.Blowup π Z' := by
  obtain ⟨hB, hA⟩ := GlobalTheory.T.isClosed_cartier_locus_support g Z h₀ h₁ h₂
  let A : Closeds X₁ := ⟨_, hA⟩
  let O₁ : X₁.Opens := ⟨_, hB.isOpen_compl⟩
  let O₂ : X₁.Opens := ⟨_, hA.isOpen_compl⟩
  have hO₁ : (O₁ : Set X₁) = ((Z.support : Set X₁) \ A)ᶜ := by
    ext x
    change ¬ (x ∈ Z.support ∧ CartAt Z x) ↔ ¬ (x ∈ Z.support ∧ ¬ (x ∈ Z.support ∧ ¬ CartAt Z x))
    tauto
  obtain ⟨c₁, c₂⟩ := GlobalTheory.T.vanishing_ideal_smooth_agrees_off g Z A O₁ h₂ (fun x hx => hx.1) hO₁
  have hV : FinalTheorems.EffCartier (Z.comap V.ι) := GlobalTheory.effCartier_comap_of_isIso_restrict π Z V h₄ h₃.1
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal A).support : Set X₁) = A :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal A
  refine ⟨_, c₁, ?_, GlobalTheory.T.blowup_of_agreeing_ideal_cartier π Z _ O₁ O₂ h₃ ?_ c₂ ?_ ?_⟩
  · rw [hsupp]
    intro x hx hxV
    exact hx.2 ((GlobalTheory.T.effCartier_restrict_iff_cartier_at Z V).1 hV x hxV)
  · refine top_le_iff.1 fun x _ => ?_
    by_cases hx : x ∈ Z.support ∧ CartAt Z x
    · exact Or.inr fun h => h.2 hx.2
    · exact Or.inl hx
  · intro x hx hx'
    rw [← SetLike.mem_coe, hsupp] at hx'
    exact hx hx'
  · refine (GlobalTheory.T.effCartier_restrict_iff_cartier_at Z O₂).2 fun x hx => ?_
    by_contra hc
    exact hx ⟨by_contra fun h => hc (GlobalTheory.T.cartier_at_of_not_mem_support Z x h), hc⟩

theorem isIntegral_of_seq {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) :
    Nonempty X' → Smooth (s ≫ g) → IsIntegral X' := by
  induction h with
  | id => exact fun _ _ => hX
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn hsm
    have : Nonempty X₁ := ⟨π hn.some⟩
    exact GlobalTheory.T.isIntegral_blowup_of_smooth (s ≫ g) Z π (ih this h₂) h₅ (by simpa using hsm) hn

theorem seq_of_iso {k : Type} [Field k] {X X' : Scheme.{0}} {g : X ⟶ Sp k} {E : Closeds X} {s : X' ⟶ X}
    {E' : Closeds X'} (h : IsSncBlowupSeq g E s E') (hX : IsIntegral X) (hg : IsProjOver g) :
    Nonempty X' → ∀ V : X.Opens, IsIso (s ∣_ V) → IsSmoothBlowupSeq g (V : Set X)ᶜ s := by
  induction h with
  | id => exact fun _ _ _ => .id
  | @step X₁ X₂ s E₁ Z π h₁ h₂ h₃ h₄ h₅ ih =>
    intro hn V hV
    have : Nonempty X₁ := ⟨π hn.some⟩
    have hi : IsIntegral X₁ := isIntegral_of_seq h₁ hX this h₂
    have hp : IsProjOver (s ≫ g) :=
      (Resolution.IsBlowupSeq.of_smooth h₁.isSmoothBlowupSeq).isProjOver hg
    have hP : IsProper (s ≫ g) := isProper_of_isProjOver hp
    have hs : IsSeparated s := IsSeparated.of_comp s g
    obtain ⟨a, b⟩ := GlobalTheory.T.isIso_restrict_of_blowup_comp s π Z V hi hs h₅ hn hV
    obtain ⟨Z', c₁, c₂, c₃⟩ := exists_centre_off (s ≫ g) Z π (s ⁻¹ᵁ V) h₂ hi h₃ h₅ b
    exact .step Z' π (ih this V a) c₁ c₂ c₃

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂


end GlobalTheory.CompanionTheory.Hypotheses₂
end
end
end

-- Source module: Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationClosed

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem principalisation_closed : GlobalTheory.Published.Principalisation := by
  intro k _ _ d Y f hY hd hp I hI
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hP : IsProper f := isProper_of_isProjOver hp
  obtain ⟨X', s, E', hseq, hsm', hcart, hsnc, hiso⟩ :=
    principalisationCharZero_bot_closed k d Y f hd inferInstance inferInstance I (not_subset_of_ne_bot hI)
  obtain ⟨y, hy⟩ := GlobalTheory.Principalise.nonempty_compl_support hI
  have hne : Nonempty X' := by
    obtain ⟨w, hw⟩ := (s ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
    exact ⟨(s ⁻¹ᵁ I.support.compl).ι w⟩
  have hint : IsIntegral X' := isIntegral_of_seq hseq hY hne hsm'
  have hproj : IsProjOver (s ≫ f) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hp
  have hdense : Dense ((s ⁻¹ᵁ I.support.compl : X'.Opens) : Set X') := by
    have := dense_compl_of_snc _ hsnc
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this.mono fun x hx => hx
  have hrel : SmoothOfRelativeDimension d (s ≫ f) :=
    relDim_of_dense _ _ hdense (relDim_preimage s f _ (by
      have : SmoothOfRelativeDimension (0 + d) (Scheme.Opens.ι I.support.compl ≫ f) := inferInstance
      simpa using this))
  have hc := seq_of_iso hseq hY hp hne I.support.compl hiso
  refine ⟨X', s, hint, hrel, hproj, hc.mono ?_, hiso, hcart, hsnc⟩
  intro x hx
  simpa using hx

end PositivityTheory.ResPlug.WeightsCompactStabilizer
end
end
end
