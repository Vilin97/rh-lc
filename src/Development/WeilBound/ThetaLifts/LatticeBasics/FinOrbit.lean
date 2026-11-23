module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Baire.LocallyCompactRegular
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.HermAbs

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Herm

open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem exists_rep (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] :
    ∃ T : U →ₗ[ℂ] Y, ∀ x, ∀ y ∈ Y, ⟪(T x : U), y⟫_ℂ = b x y := by
  have := FiniteDimensional.complete ℂ Y
  have ex : ∀ x, ∃ t : Y, ∀ y : Y, ⟪t, y⟫_ℂ = b x y := fun x =>
    ⟨(InnerProductSpace.toDual ℂ Y).symm (LinearMap.toContinuousLinearMap (b x ∘ₗ Y.subtype)), fun y => by simp⟩
  choose t ht using ex
  refine ⟨⟨⟨t, fun x x' => ext_inner_right ℂ fun y => ?_⟩, fun c x => ext_inner_right ℂ fun y => ?_⟩, fun x y hy => ht x ⟨y, hy⟩⟩
  · simp [inner_add_left, ht]
  · simp [inner_smul_left, ht]

def homsF {K : Type} [Group K] (κ : K →* Module.End ℂ U) (f : U) : Submodule ℂ (orb κ f →ₗ[ℂ] U) where
  carrier := {L | ∀ k x, L ⟨κ k x.1, span_orbit_stab κ f k _ x.2⟩ = κ k (L x)}
  add_mem' := fun {a b} ha hb k x => by simp [ha k x, hb k x]
  zero_mem' := fun k x => by simp
  smul_mem' := fun c a ha k x => by simp [ha k x]

theorem exists_eigen {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) {ι : Type} [Finite ι] (l : ι → U →ₗ[ℂ] ℂ)
    (hl : ∀ x, (∀ i k, l i (κ k x) = 0) → x = 0) (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (κ k x) (κ k y) = b x y)
    (f : U) (h0 : f ≠ 0) : ∃ (x : U) (c : ℂ), x ≠ 0 ∧ ∀ y, b x y = c * ⟪x, y⟫_ℂ := by
  have := hf f
  have : FiniteDimensional ℂ (homsF κ f) := by
    let ev : homsF κ f →ₗ[ℂ] (ι → Module.Dual ℂ (orb κ f)) :=
      LinearMap.pi fun i => (LinearMap.llcomp ℂ _ _ _ (l i)) ∘ₗ (homsF κ f).subtype
    refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun L hL => Subtype.ext (LinearMap.ext fun x => ?_))
    refine hl _ fun i k => ?_
    rw [← L.2 k x]
    exact LinearMap.congr_fun (congrFun hL i) _
  let Z : Submodule ℂ U := Submodule.map₂ (LinearMap.id : (orb κ f →ₗ[ℂ] U) →ₗ[ℂ] _) (homsF κ f) ⊤
  have fZ : FiniteDimensional ℂ Z := Module.Finite.iff_fg.2
    (Submodule.FG.map₂ _ (Module.Finite.iff_fg.1 inferInstance) (Module.Finite.fg_top))
  have mZ : ∀ L ∈ homsF κ f, ∀ x, L x ∈ Z := fun L hL x => Submodule.apply_mem_map₂ _ hL trivial
  have sZ : ∀ k, ∀ z ∈ Z, κ k z ∈ Z := fun k => show Z ≤ Z.comap (κ k) from
    Submodule.map₂_le.2 fun L hL x _ => by
      show κ k (L x) ∈ Z
      rw [← hL k x]; exact mZ L hL _
  have orth : ∀ y ∈ Zᗮ, ∀ z ∈ Z, b z y = 0 := fun y hy => by
    have := hf y
    have yZ : orb κ y ≤ Zᗮ := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact orth_stab κ hi Z sZ k y hy)
    obtain ⟨T, hT⟩ := exists_rep b (orb κ y)
    have eq : ∀ k x, (T (κ k x) : U) = κ k (T x) := fun k x => by
      have : T (κ k x) = ⟨κ k (T x), span_orbit_stab κ y k _ (T x).2⟩ := ext_inner_right ℂ fun u => by
        have e : (u : U) = κ k (κ k⁻¹ u) := by rw [← Module.End.mul_apply, ← map_mul]; simp
        show ⟪(T (κ k x) : U), (u : U)⟫_ℂ = ⟪κ k (T x), (u : U)⟫_ℂ
        rw [hT _ _ u.2, e, hb, hi, hT _ _ (span_orbit_stab κ y k⁻¹ _ u.2)]
      rw [this]
    refine show Z ≤ LinearMap.ker (b.flip y) from Submodule.map₂_le.2 fun L hL x _ => ?_
    show b (L x) y = 0
    have h1 : (T (L x) : U) ∈ Z := mZ ((orb κ y).subtype ∘ₗ T ∘ₗ L) (fun k x => by
      show (T (L _) : U) = κ k (T (L x))
      rw [hL k x, eq]) x
    rw [← hT _ _ (mem_orb κ y)]
    exact hy _ h1
  obtain ⟨T, hT⟩ := exists_rep b Z
  have : Nontrivial Z := ⟨⟨f, mZ (orb κ f).subtype (fun _ _ => rfl) ⟨f, mem_orb κ f⟩⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T ∘ₗ Z.subtype)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨x, starRingEnd ℂ c, fun h => hx.2 (Subtype.ext h), fun y => ?_⟩
  have e : T x = c • x := hx.apply_eq_smul
  have hy := Z.sub_starProjection_mem_orthogonal y
  have e1 := orth _ hy x x.2
  have e2 := hy _ x.2
  rw [map_sub, sub_eq_zero] at e1
  rw [inner_sub_right, sub_eq_zero] at e2
  rw [e1, e2, ← hT _ _ (Z.starProjection_apply_mem y), e, Submodule.coe_smul, inner_smul_left]

end GlobalTheory.ThK.Dbl.Herm

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LatticeBasics.FinOrbit

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Herm

open scoped InnerProductSpace Cardinal
open PositivityTheory.ThKF.Abs Topology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P : Type} [AddCommGroup P] [Module ℂ P]

theorem fin_orbit [BaireSpace G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hu : Function.Injective u)
    (hc : ∀ x, Continuous (u x)) (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ P ≤ ℵ₀) (x : P) {C : Set G}
    (hC : IsCompact C) : ∃ V : Submodule ℂ P, FiniteDimensional ℂ V ∧ ∀ g ∈ C, ρ g x ∈ V := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ P
  have : Countable (Module.Basis.ofVectorSpaceIndex ℂ P) := Cardinal.mk_le_aleph0_iff.1 (b.mk_eq_rank''.trans_le hr)
  let V : Finset (Module.Basis.ofVectorSpaceIndex ℂ P) → Submodule ℂ P := fun t => Submodule.span ℂ (t.image b)
  have o : Continuous fun g => u (ρ g x) := continuous_pi fun h => by
    simp only [he]; exact (hc x).comp (continuous_const.mul continuous_id)
  obtain ⟨t, g₀, h₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun t => {g | ρ g x ∈ V t}) (fun t => by
      have : IsClosed ((V t).map u : Set (G → ℂ)) := Submodule.closed_of_finiteDimensional _
      convert this.preimage o using 1
      ext g
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => (hu e ▸ hy : ρ g x ∈ V t)⟩)
    (Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨(b.repr (ρ g x)).support, by
      simpa [V] using b.mem_span_repr_support (ρ g x)⟩)
  refine hC.induction_on ⟨⊥, inferInstance, by simp⟩ (fun s s' h ⟨W, h1, h2⟩ => ⟨W, h1, fun g hg => h2 g (h hg)⟩)
    (fun s s' ⟨W, h1, h2⟩ ⟨W', h1', h2'⟩ => ⟨W ⊔ W', inferInstance, fun g hg =>
      hg.elim (fun h => Submodule.mem_sup_left (h2 g h)) fun h => Submodule.mem_sup_right (h2' g h)⟩) fun k _ => ?_
  refine ⟨(fun g => g₀ * k⁻¹ * g) ⁻¹' {g | ρ g x ∈ V t}, mem_nhdsWithin_of_mem_nhds
    ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 h₀)),
    (V t).map (ρ (k * g₀⁻¹)), inferInstance, fun g hg => ⟨_, hg, ?_⟩⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem line [LocallyCompactSpace G] [T2Space G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hc : ∀ x, Continuous (u x))
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (hK' : IsCompact (K : Set G)) {Ω : Set G} (hΩ : IsCompact Ω)
    (cov : ∀ g, ∃ g' ∈ Ω, ∀ x, u x g = u x g') (b c : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (hb : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (hi : ∀ g x y, c (ρ g x) (ρ g y) = c x y)
    (hs : ∀ x y, starRingEnd ℂ (c y x) = c x y) (hp : ∀ x, 0 ≤ (c x x).re) (hd : ∀ x, c x x = 0 → u x = 0)
    (b1 : LinearMap.ker u ≤ b.ker) (b2 : LinearMap.ker u ≤ b.flip.ker) (c2 : LinearMap.ker u ≤ c.flip.ker)
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, b x y = lam * c x y := by
  by_cases h0 : ∀ x, u x = 0
  · exact ⟨0, fun x y => by rw [b1 (h0 x)]; simp⟩
  push Not at h0
  obtain ⟨f, hf⟩ := h0
  have c1 : LinearMap.ker u ≤ c.ker := fun x hx => LinearMap.ext fun y => by
    rw [← hs, show c y x = 0 from LinearMap.congr_fun (c2 hx) y]; simp
  have st : ∀ g, LinearMap.ker u ≤ (LinearMap.ker u).comap (ρ g) := fun g x hx => funext fun h => by
    rw [he, show u x = 0 from hx]; rfl
  let U := P ⧸ LinearMap.ker u
  let π : P →ₗ[ℂ] U := (LinearMap.ker u).mkQ
  have sj : ∀ z : U, ∃ x, π x = z := (LinearMap.ker u).mkQ_surjective
  let b' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ b b1 b2
  let c' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ c c1 c2
  let ρ' : G →* Module.End ℂ U :=
    { toFun := fun g => Submodule.mapQ _ _ (ρ g) (st g)
      map_one' := LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp)
      map_mul' := fun g h => LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp) }
  let u' : U →ₗ[ℂ] (G → ℂ) := (LinearMap.ker u).liftQ u le_rfl
  have iu : Function.Injective u' := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  let core : InnerProductSpace.Core ℂ U :=
    { inner := fun x y => c' x y
      conj_inner_symm := fun z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hs x y
      re_inner_nonneg := fun z => by obtain ⟨x, rfl⟩ := sj z; exact hp x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun z hz => by obtain ⟨x, rfl⟩ := sj z; exact (Submodule.Quotient.mk_eq_zero _).2 (hd x hz) }
  letI : NormedAddCommGroup U := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ U := InnerProductSpace.ofCore core.toCore
  obtain ⟨t, -, ht⟩ := hΩ.elim_nhds_subcover (fun g => (fun h => g⁻¹ * h) ⁻¹' K) fun g _ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (hK.mem_nhds (by simpa using K.one_mem))
  obtain ⟨z, lam, hz, e⟩ := exists_eigen (U := U) (ρ'.comp K.subtype)
    (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hi k x y)
    (fun z => by
      obtain ⟨V, h1, h2⟩ := fin_orbit ρ' u' iu (fun z => by obtain ⟨x, rfl⟩ := sj z; exact hc x)
        (fun g z h => by obtain ⟨x, rfl⟩ := sj z; exact he g x h) (u.quotKerEquivRange.rank_eq.trans_le hr) z hK'
      exact Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k k.2)))
    (fun i : t => LinearMap.proj i.1 ∘ₗ u')
    (fun z hz => by
      obtain ⟨x, rfl⟩ := sj z
      refine (Submodule.Quotient.mk_eq_zero _).2 (funext fun g => ?_)
      obtain ⟨g', h1, h2⟩ := cov g
      obtain ⟨i, hi, h3⟩ := Set.mem_iUnion₂.1 (ht h1)
      have : u (ρ (i⁻¹ * g') x) i = 0 := hz ⟨i, hi⟩ ⟨_, h3⟩
      rwa [he, mul_inv_cancel_left, ← h2] at this)
    b' (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hb k x y) (π f)
    (fun h => hf ((Submodule.Quotient.mk_eq_zero _).1 h))
  obtain ⟨x₀, rfl⟩ := sj z
  let N : Submodule ℂ P := LinearMap.ker (b - lam • c)
  have mN : ∀ x, x ∈ N ↔ ∀ y, b x y = lam * c x y := fun x => by
    simp [N, LinearMap.ext_iff, sub_eq_zero]
  refine (irr N (fun x hx => (mN x).2 fun y => ?_) fun g x hx => (mN _).2 fun y => ?_).elim
    (fun h => absurd ((Submodule.Quotient.mk_eq_zero _).2 (h ((mN x₀).2 fun y => e (π y)))) hz)
    fun h => ⟨lam, fun x => (mN x).1 (h ▸ trivial)⟩
  · rw [b1 hx, c1 hx]; simp
  · rw [show y = ρ g (ρ g⁻¹ y) by rw [← Module.End.mul_apply, ← map_mul]; simp, hb, hi, (mN x).1 hx]

end GlobalTheory.ThK.Dbl.Herm

end
end
end
