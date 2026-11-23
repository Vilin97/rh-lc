module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBound
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompatStatement
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoordsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dominant_smooth_map_coords : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | exact GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartSmooth.smooth_chartRing <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGenerated

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartFrac

theorem exists_eq_div_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  intro X Ω _ ξ κ x h c hc a
  have hchart : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc, fun c' => TieArith.mem_regAt_genCpt ξ h.gen _⟩
  obtain ⟨t, ht, hu, hta⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c (TieArith.genCpt ξ) hchart a).mp
    (TieArith.mem_regAt_genCpt ξ h.gen a)
  exact ⟨t * a, hta, t, ht, hu.1, (mul_div_cancel_left₀ a hu.1).symm⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrac
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGeneratedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.fraction_field_coords_generated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | exact GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBoundStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kaehler_rank_localization_bound : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | exact GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalStep.local_step <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegree

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Kaehler

theorem finrank_kaehlerDifferential_of_adjoin_eq_top (K L : Type) [Field K] [Field L] [Algebra K L]
    (I : Type) [Fintype I] (u : I → L) (hu : AlgebraicIndependent K u)
    (hadj : IntermediateField.adjoin K (Set.range u) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  classical
  letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra
  have hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q :=
    fun _ => rfl
  have : IsScalarTower K (MvPolynomial I K) L :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]
  have : FaithfulSMul (MvPolynomial I K) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hu
  have : IsFractionRing (MvPolynomial I K) L := IsFractionRing.of_field (MvPolynomial I K) L fun z => by
    have hz : z ∈ IntermediateField.adjoin K (Set.range u) := by rw [hadj]; trivial
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_range_iff K u z).1 hz
    exact ⟨r, s, h⟩
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L
  rw [Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]

end GlobalTheory.CompanionTheory.Kaehler
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegreeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kaehler_rank_transcendence_degree : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (I : Type) [Fintype I] (u : I → L),
    AlgebraicIndependent K u → IntermediateField.adjoin K (Set.range u) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | exact GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | (intros; apply GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoords

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncPull
open GlobalTheory.CompanionTheory.Ar.SncRefine

theorem adjoin_insert_eq {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) :
    Algebra.adjoin ℚ (insert t ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω) : Set Ω)) =
      Algebra.adjoin ℚ (insert t (Set.range (bratio y c))) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro b (rfl | hb)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · have h : Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) ≤
          (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).restrictScalars ℤ := Algebra.adjoin_le (by
        rintro _ ⟨d, rfl⟩
        exact seg_ratio_mem y c (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).toSubring
          (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) d)
      exact h hb
  · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
    rintro _ ⟨p, rfl⟩
    obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩

theorem map_mem_adjoin {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    {W : Set Ω₀} {W' : Set Ω} (hW : ∀ w ∈ W, algebraMap Ω₀ Ω w ∈ W') {b : Ω₀} (hb : b ∈ Algebra.adjoin ℚ W) :
    algebraMap Ω₀ Ω b ∈ Algebra.adjoin ℚ W' := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hW x hx)
  | algebraMap r =>
    have : algebraMap Ω₀ Ω (algebraMap ℚ Ω₀ r) = algebraMap ℚ Ω r := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_cover {R : Type} [CommRing R] (G : R → Prop) (h : ∀ P : Ideal R, P.IsPrime → ∃ t, t ∉ P ∧ G t) :
    ∃ (m : ℕ) (f a : Fin m → R), ∑ l, a l * f l = 1 ∧ ∀ l, G (f l) := by
  classical
  have hs : Ideal.span {t | G t} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht, hG⟩ := h M hM.isPrime
    exact ht (hle (Ideal.subset_span hG))
  have h1 : (1 : R) ∈ Ideal.span {t | G t} := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : R), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x • (x : R)

theorem isSncModel_pull : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  classical
  intro X X' Ω₀ Ω _ _ _ _ _ ξ ξ' f K _ J _ y N x' e bd I _ u hq hq' tie tie' hd hsm hu hadj hsnc c₁ hc₁
  let c : (k : K) → J k := fun k => c₁ (Sum.inr k)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc₁ (Sum.inr k) (show algebraMap Ω₀ Ω (y ⟨k, c k⟩) = 0 by rw [h, map_zero])
  have hv : ∀ p, algebraMap Ω₀ Ω (bratio y c p) = bratio (addY y x') c₁ (addV J N p) := fun p => map_div₀ _ _ _
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hxc₁ : seg (addY y x') c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc₁ k
  have hblk : ∀ p, bratio (addY y x') c₁ p ∈
      Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁) := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio (addY y x') c₁ hc₁ p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  obtain ⟨φ, hφ, hφs⟩ := GlobalTheory.T.dominant_smooth_map_coords X X' Ω₀ Ω ξ ξ' f (algebraMap Ω₀ Ω) _ _ (seg y) (seg (addY y x'))
    hq hq' tie tie' hd hsm c c₁ hxc hxc₁ (fun d => by
      have e1 : seg y d / seg y c = ∏ k, bratio y c ⟨k, d k⟩ := (Finset.prod_div_distrib _ _).symm
      rw [e1, map_prod]
      refine prod_mem fun k _ => ?_
      rw [hv]
      exact hblk _)
  obtain ⟨m, f₀, a₀, hf, ha, hsum, H⟩ := hsnc c hc
  have hfin := GlobalTheory.T.kaehler_rank_transcendence_degree Ω₀ Ω I u hu hadj
  have hW : ∀ w ∈ Set.range (bratio y c), algebraMap Ω₀ Ω w ∈ Set.range (bratio (addY y x') c₁) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hv p).symm⟩
  let R₁ := Algebra.adjoin ℚ (Set.range (bratio (addY y x') c₁))
  have hfr : ∀ (A : Subalgebra ℤ Ω₀) (S : Subalgebra ℚ Ω₀), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω₀, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω₀ := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hfr₁ : ∀ (A : Subalgebra ℤ Ω) (S : Subalgebra ℚ Ω), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hloc : ∀ P : Ideal R₁, P.IsPrime → ∃ t : R₁, t ∉ P ∧ ((t : Ω) ≠ 0 → ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range (bratio (addY y x') c₁))) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + Fintype.card I) → S') (n' : ℕ), n' ≤ e + Fintype.card I ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename (addV J N)), ∀ s : S',
              (s : Ω) = MvPolynomial.aeval (bratio (addY y x') c₁) g → s ∈ q) ↔
            ∃ i : Fin (e + Fintype.card I), (i : ℕ) < n' ∧ z' i ∈ q)) := by
    intro P hP
    let fl : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (f₀ l), map_mem_adjoin hW (hf l)⟩
    let al : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (a₀ l), map_mem_adjoin hW (ha l)⟩
    have hone : ∑ l, al l * fl l = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      show ∑ l, algebraMap Ω₀ Ω (a₀ l) * algebraMap Ω₀ Ω (f₀ l) = 1
      simp only [← map_mul]

      rw [← map_sum, hsum, map_one]
    obtain ⟨l, hl⟩ : ∃ l, fl l ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hcon l)))
    have h0 : f₀ l ≠ 0 := fun h => hl (by
      have : fl l = 0 := Subtype.ext (by show algebraMap Ω₀ Ω (f₀ l) = 0; rw [h, map_zero])
      rw [this]
      exact P.zero_mem)
    obtain ⟨hSm, z, n, hn, hli, hspan, hbd⟩ := H l h0 _ rfl
    have hle₀ : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ Algebra.adjoin ℚ
        ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω₀) : Set Ω₀) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
        rw [hd]
        exact Algebra.subset_adjoin (Algebra.subset_adjoin ⟨d, rfl⟩))
    obtain ⟨ψ, hψ, hψs⟩ := GlobalTheory.T.smooth_map_localization_compat Ω₀ Ω _ _ φ hφ hφs (f₀ l) (hle₀ (hf l)) h0
      (Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))))
      (Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))))
      (adjoin_insert_eq y c hc _).symm (adjoin_insert_eq (addY y x') c₁ hc₁ _).symm
    have hA₀ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c),
        a ∈ Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))) := fun a ha' => by
      rw [← adjoin_insert_eq y c hc]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    have hA₁ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁),
        a ∈ Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))) := fun a ha' => by
      rw [← adjoin_insert_eq (addY y x') c₁ hc₁]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    obtain ⟨t, ht, hG⟩ := GlobalTheory.T.kaehler_rank_localization_bound Ω₀ Ω _ _ (bratio y c) (bratio (addY y x') c₁) (addV J N) hv e _ bd hfin (f₀ l) h0 _ _ rfl rfl
      ψ hψ hψs (hfr _ _ hA₀ (GlobalTheory.T.fraction_field_coords_generated X Ω₀ ξ _ (seg y) tie c hxc))
      (hfr₁ _ _ hA₁ (GlobalTheory.T.fraction_field_coords_generated X' Ω ξ' _ (seg (addY y x')) tie' c₁ hxc₁)) hSm z n hn hli hspan hbd P hP (fl l) rfl hl
    exact ⟨t, ht, fun _ => hG⟩
  obtain ⟨m', f', a', hs', hG⟩ := exists_cover _ hloc
  refine ⟨m', fun l => (f' l : Ω), fun l => (a' l : Ω), fun l => (f' l).2, fun l => (a' l).2, ?_, fun l hl S' hS' => ?_⟩
  · have := congrArg (Subtype.val) hs'
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this
  · obtain ⟨h1, z', n', h2, h3, h4, h5⟩ := hG l hl S' hS'
    exact ⟨h1, z', n', h2, h3, h4, h5⟩

end GlobalTheory.CompanionTheory.Ar.SncPull
end
end
end
