module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pretransitive
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFiniteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionRationalToAdelicStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactPartClosedOrbit

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem compact_part_closed_orbit :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] (V : Type) [TopologicalSpace V]
      [T2Space V] [LocallyCompactSpace V] (a : G → V → V),
      (Continuous fun p : G × V => a p.1 p.2) → (∀ y, a 1 y = y) →
      (∀ g h y, a (g * h) y = a g (a h y)) →
      ∀ (Z : Set V) (x : V), IsClosed Z → (∀ y, y ∈ Z ↔ ∃ g, a g x = y) →
      ∀ Ω : Set V, IsCompact Ω → ∃ C : Set G, IsCompact C ∧ ∀ y ∈ Ω, y ∈ Z → ∃ c ∈ C, a c x = y := by
  intro G _ _ _ _ _ _ V _ _ _ a ha h1 hmul Z x hZ hZx Ω hΩ
  have hmem : ∀ (g : G) (z : Z), a g z ∈ Z := by
    intro g z
    obtain ⟨h, hh⟩ := (hZx z).1 z.2
    exact (hZx _).2 ⟨g * h, by rw [hmul, hh]⟩
  letI : MulAction G Z :=
    { smul := fun g z => ⟨a g z, hmem g z⟩
      one_smul := fun z => Subtype.ext (h1 z)
      mul_smul := fun g h z => Subtype.ext (hmul g h z) }
  haveI : ContinuousSMul G Z :=
    ⟨Continuous.subtype_mk
      (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      (fun p => hmem p.1 p.2)⟩
  haveI : MulAction.IsPretransitive G Z := by
    refine ⟨fun z w => ?_⟩
    obtain ⟨g, hg⟩ := (hZx z).1 z.2
    obtain ⟨h, hh⟩ := (hZx w).1 w.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show a (h * g⁻¹) z = w
    rw [← hg, ← hmul, inv_mul_cancel_right, hh]
  haveI : LocallyCompactSpace Z := hZ.locallyCompactSpace
  haveI : BaireSpace Z := BaireSpace.of_t2Space_locallyCompactSpace
  have hx : x ∈ Z := (hZx x).2 ⟨1, h1 x⟩
  have hopen := isOpenMap_smul_of_sigmaCompact (G := G) (X := Z) ⟨x, hx⟩
  choose K hK hKn using fun g : G => exists_compact_mem_nhds g
  have hS : IsCompact ((Subtype.val : Z → V) ⁻¹' Ω) :=
    hZ.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun g => (fun h : G => h • (⟨x, hx⟩ : Z)) '' interior (K g))
    (fun g => hopen _ isOpen_interior) (by
      intro z _
      obtain ⟨g, hg⟩ := (hZx z).1 z.2
      exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hKn g), Subtype.ext hg⟩)
  refine ⟨⋃ g ∈ t, K g, t.isCompact_biUnion fun g _ => hK g, ?_⟩
  intro y hyΩ hyZ
  have hy := ht (show (⟨y, hyZ⟩ : Z) ∈ (Subtype.val : Z → V) ⁻¹' Ω from hyΩ)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨g, hgt, c, hc, hcy⟩ := hy
  exact ⟨c, Set.mem_biUnion hgt (interior_subset hc), congrArg Subtype.val hcy⟩

end GlobalTheory.CompanionTheory.Adelic
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentative

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Proper

theorem compact_gram_fibre :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 →
      ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω →
      ∃ C : Set (HA (AF F) σ J), IsCompact C ∧
        ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) →
          ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ n X hX Ω hΩ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ (AF F)
  haveI := htg
  haveI := hlcH
  haveI := hscH
  haveI := ht2H
  obtain ⟨-, hlcK, -, ht2K, -, -, -, -, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)
  haveI := hlcK
  haveI := ht2K
  obtain ⟨hcont, h1, hmul, hinv⟩ := hact n
  obtain ⟨-, hrat, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hσ M J hJ
  have hZ : IsClosed {Y : Fin n → Fin M → AF F ⊗[F] E |
      gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} :=
    isClosed_eq (hgram n M J) continuous_const
  have hZx : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Y ∈ {Y : Fin n → Fin M → AF F ⊗[F] E |
        gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F))} ↔
      ∃ g : HA (AF F) σ J, actW (AF F) σ J g (ratTup (AF F) X) = Y := by
    intro Y
    constructor
    · intro hY
      exact GlobalTheory.T.witt_extension_rational_to_adelic F E σ hσ M J hJ n X Y hX hY
    · rintro ⟨g, rfl⟩
      show gramR (AF F) σ J _ = _
      rw [hinv, hrat]
  obtain ⟨C, hC, hCY⟩ := GlobalTheory.CompanionTheory.Adelic.compact_part_closed_orbit (HA (AF F) σ J)
    (Fin n → Fin M → AF F ⊗[F] E) (fun g Y => actW (AF F) σ J g Y) hcont h1 hmul _
    (ratTup (AF F) X) hZ hZx Ω hΩ
  exact ⟨C, hC, fun Y hY hg => hCY Y hY hg⟩

end GlobalTheory.CompanionTheory.SW.Proper
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentativeStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_orbit_compact_representative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 → ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω → ∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | exact GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre <;> assumption)
end
end
