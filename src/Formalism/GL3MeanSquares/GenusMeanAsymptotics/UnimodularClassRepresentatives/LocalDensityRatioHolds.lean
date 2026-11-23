module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AkCountEqRedCountMul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemLocFOfSmulMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqMapMulKer
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqOfMap
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexSSubInfEq
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeMemOfMemSmulTop

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  let := hA₀
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd (A₀ := A₀) inferInstance hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← mul_apply_eq_comp, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  let := hA₀
  let := hB₀
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub (A₀ := A₀) (B₀ := B₀) inferInstance inferInstance h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatioHolds

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_sSub_inf (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_sSub_inf_eq hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  refine ⟨h1, ?_⟩
  rw [h3]
  exact relIndex_hermL hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭 h2

end Formalism.HermitianLattices.Ext.L3.D2

namespace Formalism.HermitianLattices.Ext.L3

open D2

theorem local_density_ratio_holds :
    ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
      Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
        [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (A₀ B₀ : Submodule (𝓞 K) V)
        (𝔭 : Ideal (𝓞 F)),
        h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → Submodule.IsFullLattice K A₀ →
        Submodule.IsFullLattice K B₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h A₀ →
        Formalism.HermitianLatticesTheory.IsIntegralLat h B₀ →
        alphaL h (locF 𝔭 A₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
            orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
          alphaL h (locF 𝔭 B₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 A₀) 𝔭) *
            orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  intro K F _ _ _ _ _ _ hK hF V _ _ _ _ _ h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  obtain ⟨c₁, hc₁⟩ := D2.relIndex_sSub_inf hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  obtain ⟨c₂, hc₂⟩ := D2.relIndex_nSub hK hF hA₀ hB₀ h𝔭
  set c := c₁ + c₂ with hc
  obtain ⟨k₁, hk₁⟩ := hc₁ c (by omega)
  obtain ⟨k₂, hk₂⟩ := hc₂ c (by omega)
  obtain ⟨k₃, hk₃⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₄, hk₄⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  obtain ⟨k₅, hk₅⟩ := D2.relIndex_inf_glSub hK hF hs hd hA₀ hA₀i hB₀ h𝔭
  obtain ⟨k₆, hk₆⟩ := D2.relIndex_inf_glSub hK hF hs hd hB₀ hB₀i hA₀ h𝔭
  obtain ⟨k₇, hk₇⟩ := D2.nSub_le_glSub hB₀ hA₀ h𝔭
  obtain ⟨k₈, hk₈⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₉, hk₉⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  set k := k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇ + k₈ + k₉ with hk
  obtain ⟨hJI, hIJ⟩ := hk₁ k (by omega)
  obtain ⟨hNN, hNNi⟩ := hk₂ k (by omega)
  have hakA := hk₃ k (by omega)
  have hakB := hk₄ (k + c) (by omega)
  have horbAB := hk₅ k (by omega)
  have horbBA := hk₆ (k + c) (by omega)
  have hNBA := hk₇ (k + c) (by omega)
  have hαA := hk₈ k (by omega)
  have hαB := hk₉ (k + c) (by omega)
  have f1 := D2.nSub_le_sSub hF hA₀i h𝔭 k
  have f2 := D2.nSub_le_sSub hF hB₀i h𝔭 (k + c)
  have hNJ : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) :=
    le_inf f2 hNBA
  have hIS : sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k := inf_le_left
  have hJS : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) :=
    inf_le_left
  have e1 := Subgroup.relIndex_mul_relIndex (hHK := hNN) (hKL := f1)
  have e2 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJI)
  have e3 := Subgroup.relIndex_mul_relIndex (hHK := hNJ.trans hJI) (hKL := hIS)
  have e4 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJS)
  have e5 : (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) *
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)) *
        ((sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
            (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k)) := by
    rw [mul_comm, e1, ← e3, ← e2, mul_assoc]
  have E : akCount h (locF 𝔭 A₀) 𝔭 k * Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) *
      Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) * orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
      akCount h (locF 𝔭 B₀) 𝔭 (k + c) * orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) *
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    rw [hakA, hakB, ← horbAB, ← horbBA, ← hNNi, ← hIJ, ← e4, e5]
    ring
  have hQ : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast fun h0 => hb (Ideal.absNorm_eq_zero_iff.mp h0)
  have Er : (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V ^ 2 * c) *
      (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
        (orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) : ℝ) =
      (akCount h (locF 𝔭 B₀) 𝔭 (k + c) : ℝ) * (orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) : ℝ) *
        (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    exact_mod_cast E
  rw [hαA, hαB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)]
  apply mul_right_cancel₀ (pow_ne_zero (finrank K V ^ 2 * c) hQ)
  linear_combination ((Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)) * Er

end Formalism.HermitianLattices.Ext.L3
end
end
end
