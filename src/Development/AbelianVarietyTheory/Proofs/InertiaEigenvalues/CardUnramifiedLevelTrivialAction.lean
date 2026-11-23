module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import ReciprocityTheory.NeutralLocalFields.Duality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
public import ReciprocityTheory.GroupCohomology.CardLenStatement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.GroupCohomology.MemZpowersQuot
public import ReciprocityTheory.GroupCohomology.ModelComparisonDegreeZeroBijective

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.UnramA

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

noncomputable section

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation R G M)

def qRho (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : Representation R (G ⧸ N) M :=
  QuotientGroup.lift N rho (fun σ hσ => LinearMap.ext (hN σ hσ))

abbrev qT (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : TRep R (G ⧸ N) where
  V := M
  rho := qRho N rho hN
  cont := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact hrho.comp (continuous_id.prodMk continuous_const)

variable {N rho}

theorem exists_desc1 (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : G → M) (hc : c ∈ Z1 rho) (h0 : ∀ σ ∈ N, c σ = 0) :
    ∃ c' : G ⧸ N → M, c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN) ∧ ∀ g, c' (QuotientGroup.mk g) = c g := by
  have hw : ∀ a b : G, QuotientGroup.leftRel N a b → c a = c b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h2 := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨fun q => Quotient.liftOn' q c hw, ⟨?_, ?_⟩, fun g => rfl⟩
  · exact hc.1.quotient_liftOn' hw
  · intro a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc.2 g h

theorem inflation_mem_one_cocycles (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c' : G ⧸ N → M) (hc : c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN)) :
    (fun g : G => c' (QuotientGroup.mk g)) ∈ Z1 rho :=
  ⟨hc.1.comp QuotientGroup.continuous_mk, fun g h => hc.2 (QuotientGroup.mk g) (QuotientGroup.mk h)⟩

theorem apply_eq_zero_of_mem_H1ur (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : Z1 rho)
    (hc : (Submodule.Quotient.mk c : H1 rho) ∈ H1ur rho N) (σ : G) (hσ : σ ∈ N) : c.1 σ = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val c) : H1 (rho.comp N.subtype)) = 0 := hc
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 h1
  have h3 : c.1 σ = rho σ m - m := hm ⟨σ, hσ⟩
  rw [h3, hN σ hσ, sub_self]

theorem torsion_of_finite [Finite M] (m : M) : ∃ k : ℕ, 0 < k ∧ k • m = 0 :=
  ⟨Nat.card M, Nat.card_pos, card_nsmul_eq_zero'⟩

variable [CompactSpace (G ⧸ N)] [T2Space (G ⧸ N)] [TotallyDisconnectedSpace (G ⧸ N)] [Finite M]

theorem ker_frobenius_sub_id_eq_invariants (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : LinearMap.ker (rho s - LinearMap.id) = H0 rho := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]
  refine ⟨fun h g => ?_, fun h => h s⟩
  set W := ProcyclicCohomology.stab (qT N rho hrho hN) m with hW
  have hWo : IsOpen (W : Set (G ⧸ N)) := ProcyclicCohomology.stab_isOpen (qT N rho hrho hN) m
  have hWc : IsClosed (W : Set (G ⧸ N)) := W.isClosed_of_isOpen hWo
  have hsW : (QuotientGroup.mk s : G ⧸ N) ∈ W := h
  have hz : (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ N) : Set (G ⧸ N)) ⊆ W :=
    (Subgroup.zpowers_le.2 hsW)
  have htop : (W : Set (G ⧸ N)) = Set.univ := by
    rw [← hWc.closure_eq, ← Set.univ_subset_iff, ← hs.1.closure_eq]
    exact closure_mono hz
  have : (QuotientGroup.mk g : G ⧸ N) ∈ (W : Set (G ⧸ N)) := by rw [htop]; trivial
  exact this

theorem card_quot_range (u : M →ₗ[R] M) : Nat.card (M ⧸ LinearMap.range u) = Nat.card (LinearMap.ker u) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)
  rw [Nat.card_congr u.quotKerEquivRange.toEquiv] at h2
  have h3 : 0 < Nat.card (LinearMap.range u) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left h3 h1).symm

theorem card_H1ur (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : Nat.card (H1ur rho N) = Nat.card (H0 rho) := by
  set P : Submodule R M := LinearMap.range (rho s - LinearMap.id) with hP
  let f : Z1 rho →ₗ[R] M ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 rho).subtype)
  have hker : (Bd1 rho).comap (Z1 rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk (c.1 s) : M ⧸ P) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ : H1 rho →ₗ[R] M ⧸ P := ((Bd1 rho).comap (Z1 rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hinj0 : ∀ z ∈ H1ur rho N, φ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c', hc', hcc⟩ := exists_desc1 hN c.1 c.2 (apply_eq_zero_of_mem_H1ur hN c hz)
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hz0
    obtain ⟨m, hm⟩ := hz0
    have h1 : c' (QuotientGroup.mk s) = rho s m - m := by rw [hcc, ← hm]; rfl
    have h2 := ProcyclicCohomology.cocycle_eq_of_apply (qT N rho hrho hN) hs.1 c' hc' m h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_contCoboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    change c.1 g = _
    rw [← hcc]
    exact h2 (QuotientGroup.mk g)
  have hbij : Bijective (fun x : H1ur rho N => φ x.1) := by
    constructor
    · intro x y hxy
      have h1 : φ (x.1 - y.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hxy
      exact Subtype.ext (sub_eq_zero.1 (hinj0 _ ((H1ur rho N).sub_mem x.2 y.2) h1))
    · intro y
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨c', hc', hcs⟩ := ProcyclicCohomology.exists_cocycle (qT N rho hrho hN) (ProcyclicCohomology.comm_of_dense hs.1) hs.1 hs.2 m
        (torsion_of_finite (M := M) m)
      have hZ := inflation_mem_one_cocycles hN c' hc'
      refine ⟨⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩, ?_⟩
      · change (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val ⟨_, hZ⟩) :
          H1 (rho.comp N.subtype)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        refine (mem_contCoboundaries1 _ _).2 ⟨0, fun σ => ?_⟩
        change c' (QuotientGroup.mk σ.1) = _
        rw [(QuotientGroup.eq_one_iff σ.1).2 σ.2, map_zero, sub_zero]
        have h1 : c' (1 * 1) = c' 1 + qRho N rho hN 1 (c' 1) := hc'.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at h1
        exact left_eq_add.1 h1
      · change φ (Submodule.Quotient.mk _) = _
        rw [hφ]
        exact congrArg _ hcs
  rw [Nat.card_eq_of_bijective _ hbij, hP, card_quot_range, ker_frobenius_sub_id_eq_invariants hrho hN hs]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardUnramifiedLevelTrivialAction

section

@[expose] public section

open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def LCHomLev {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (M : Type)
    [AddCommGroup M] [Module O M] (c : O) (I : Subgroup G) : Type :=
  {f : G → Lev M c // IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧ ∀ g ∈ I, f g = 0}

section Triv

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem mem_coboundaries_of_trivial {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m) (x : G → M) :
    x ∈ Formalism.NG.coB1 ρ ↔ x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    funext g
    show ρ g v - v = 0
    rw [hρ, sub_self]
  · rintro rfl
    exact zero_mem _

theorem mk_eq_zero_of_triv {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m)
    (z : Formalism.NG.coZ1s ρ) : (Submodule.Quotient.mk z : Formalism.NG.H1z ρ) = 0 ↔ (z : G → M) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    mem_coboundaries_of_trivial hρ]

variable [TopologicalSpace G]

theorem card_torsion_eq_locConstHom_trivial_action (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m)
    (I : Subgroup G) (c : O) :
    Nat.card (LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (LCHomLev M c I) := by
  have hres : ∀ (g : I) (m : M), Formalism.NG.resRep ρ I g m = m := fun g m => hρ g m
  let coc : LCHomLev M c I → Formalism.NG.coZ1s ρ := fun f =>
    ⟨fun g => (f.1 g).val, fun a b => by
      show (f.1 (a * b)).val = (f.1 a).val + ρ a (f.1 b).val
      rw [hρ, f.2.2.1, Lev.val_add]⟩
  let F : LCHomLev M c I → LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype)) := fun f =>
    ⟨⟨⟨Submodule.Quotient.mk (coc f),
        Submodule.mem_map.2 ⟨coc f, f.2.1.comp Lev.val, rfl⟩⟩,
      by
        change (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I (coc f)) :
          Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0
        rw [mk_eq_zero_of_triv hres]
        funext g
        show (f.1 g.1).val = 0
        rw [f.2.2.2 g.1 g.2]
        rfl⟩,
      by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        apply Subtype.ext
        show c • (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) = 0
        rw [← Submodule.Quotient.mk_smul, mk_eq_zero_of_triv hρ]
        funext g
        exact Lev.smul_val (f.1 g)⟩
  have hinj : ∀ f f' : LCHomLev M c I, (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) =
      Submodule.Quotient.mk (coc f') → f = f' := by
    intro f f' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_of_triv hρ] at h
    apply Subtype.ext
    funext g
    apply Lev.ext
    have h1 : (f.1 g).val - (f'.1 g).val = 0 := congrFun h g
    exact sub_eq_zero.1 h1
  refine (Nat.card_eq_of_bijective F ⟨fun f f' h => hinj f f' ?_, fun y => ?_⟩).symm
  · exact congrArg (fun y => y.1.1.1) h
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.1.1.2
    have hk : (Submodule.Quotient.mk (c • z) : Formalism.NG.H1z ρ) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      change c • Submodule.mkQ _ z = 0
      rw [hzy]
      exact congrArg (fun w => w.1.1) (LinearMap.mem_ker.1 y.2)
    rw [mk_eq_zero_of_triv hρ] at hk
    have hz0 : ∀ g, c • (z : G → M) g = 0 := fun g => congrFun hk g
    have hu : Formalism.NG.resH1 ρ I (Submodule.mkQ _ z) = 0 := by
      rw [hzy]
      exact y.1.2
    have hu' : (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I z) :
        Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0 := hu
    rw [mk_eq_zero_of_triv hres] at hu'
    have hI0 : ∀ g ∈ I, (z : G → M) g = 0 := fun g hg => congrFun hu' ⟨g, hg⟩
    let f : LCHomLev M c I := ⟨fun g => Lev.mk ((z : G → M) g) (hz0 g),
      IsLocallyConstant.desc _ Lev.val hz (fun a b h => Lev.ext h),
      fun a b => Lev.ext (by rw [Lev.val_add, Lev.val_mk, Lev.val_mk, Lev.val_mk, z.2 a b, hρ]),
      fun g hg => Lev.ext (by rw [Lev.val_mk, hI0 g hg]; rfl)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.Quotient.mk (coc f) = y.1.1.1
    rw [← hzy]
    rfl

end Triv

section H1Triv

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {N : Type}
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

theorem H1_mk_eq_zero_iff_of_trivial {rho : Representation R Γ N} (hrho : ∀ g m, rho g m = m)
    (z : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = 0 ↔ z = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    funext g
    rw [hm g, hrho, sub_self]
    rfl
  · rintro rfl
    exact ⟨0, fun g => by rw [map_zero, sub_zero]; rfl⟩

theorem mk_mem_H1ur_of_vanish (rho : Representation R Γ N) (J : Subgroup Γ) (z : Z1 rho)
    (hz : ∀ g ∈ J, z.1 g = 0) : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J := by
  change (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
    H1 (rho.comp J.subtype)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact (mem_coboundaries1 _ _).2 ⟨0, fun g => by rw [map_zero, sub_zero]; exact hz g.1 g.2⟩

theorem vanish_of_mk_mem_H1ur (rho : Representation R Γ N) (J : Subgroup Γ)
    (hJ : ∀ g ∈ J, ∀ m, rho g m = m) (z : Z1 rho)
    (hz : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J) (g : Γ) (hg : g ∈ J) : z.1 g = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
      H1 (rho.comp J.subtype)) = 0 := hz
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  have h3 : z.1 g = rho g m - m := hm ⟨g, hg⟩
  rw [h3, hJ g hg, sub_self]

end H1Triv

theorem card_LCHomLev_eq_unrK {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m) (I : Subgroup G)
    (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) (r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    letI := levZ (M := M) p r h
    Nat.card (LCHomLev M c I) =
      Nat.card (Formalism.GaloisCohomology.unrK (levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  letI := levZ (M := M) p r h
  let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  let F : LCHomLev M c I → Formalism.GaloisCohomology.unrK ρ' := fun f =>
    ⟨Submodule.Quotient.mk ⟨f.1 ∘ i.symm, (f.2.1.comp_continuous i.symm.continuous).continuous,
        fun a b => by
          show f.1 (i.symm (a * b)) = f.1 (i.symm a) + ρ' a (f.1 (i.symm b))
          rw [hρ', map_mul, f.2.2.1]⟩,
      mk_mem_H1ur_of_vanish ρ' _ _ fun g hg => by
        show f.1 (i.symm g) = 0
        exact f.2.2.2 _ ((hI _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg))⟩
  refine Nat.card_eq_of_bijective F ⟨fun f f' hff => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hff
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, H1_mk_eq_zero_iff_of_trivial hρ', sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    funext g
    have h3 := congrFun h2 (i g)
    simpa only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] using h3
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx : (Submodule.Quotient.mk z : H1 ρ') ∈ H1ur ρ' (Formalism.GaloisCohomology.inertiaK p K) := by
      rw [hz]; exact x.2
    let f : LCHomLev M c I := ⟨fun g => z.1 (i g),
      ((IsLocallyConstant.iff_continuous _).2 z.2.1).comp_continuous i.continuous,
      fun a b => by
        show z.1 (i (a * b)) = z.1 (i a) + z.1 (i b)
        rw [map_mul, z.2.2, hρ'],
      fun g hg => vanish_of_mk_mem_H1ur ρ' _ (fun σ _ m => hρ' σ m) z hx (i g) ((hI g).1 hg)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change Submodule.Quotient.mk _ = x.1
    rw [← hz]
    congr 1
    apply Subtype.ext
    funext g
    show z.1 (i (i.symm g)) = z.1 g
    rw [ContinuousMulEquiv.apply_symm_apply]


open scoped ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem card_unramifiedClasses_eq_card_invariants_localGalois {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    (rho : Representation R (Formalism.GaloisCohomology.GK p K) N) (hrho : ReciprocityTheory.Gal.ContAction rho)
    (hI : ∀ σ ∈ Formalism.GaloisCohomology.inertiaK p K, ∀ m, rho σ m = m) :
    Nat.card (Formalism.GaloisCohomology.unrK rho) = Nat.card (H0 rho) := by
  change Nat.card (Neutral.B1.H1ur rho (Neutral.B1.inertiaK p K)) = Nat.card (Neutral.B1.H0 rho)
  replace hI : ∀ σ ∈ Neutral.B1.inertiaK p K, ∀ m, rho σ m = m := hI
  rw [← ReciprocityTheory.DiscreteGroups.LocalClassField.subG_Kur_eq_inertiaK hK] at hI ⊢
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles.card_H1ur hrho hI (s := ReciprocityTheory.DiscreteGroups.LocalClassField.frobK p K)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur hK)

theorem card_unr_lev_of_triv : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {ϖ : O},
    Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O G M), (∀ g m, ρ g m = m) →
    ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) → ∀ n : ℕ,
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro p _ K hK O _ _ _ _ ϖ hϖ hp G _ _ i M _ _ e ρ hρ I hI n
  have hpn : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} :=
    Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hp) n)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI := levZ (M := M) p n hpn
  obtain ⟨hfin, hcard⟩ := levKO_card hϖ e n
  haveI := hfin
  let ρ' := levRepZ p n hpn (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  have hcont : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ']
    exact continuous_snd
  calc _ = Nat.card (LCHomLev M (ϖ ^ n) I) := card_torsion_eq_locConstHom_trivial_action ρ hρ I (ϖ ^ n)
    _ = Nat.card (Formalism.GaloisCohomology.unrK ρ') := card_LCHomLev_eq_unrK i ρ hρ I hI n (ϖ ^ n) hpn
    _ = Nat.card (H0 ρ') :=
        card_unramifiedClasses_eq_card_invariants_localGalois hK ρ' hcont (fun σ _ m => hρ' σ m)
    _ = Nat.card (Lev M (ϖ ^ n)) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x g => hρ' g x)
    _ = _ := hcard

end GlobalTheory.ShapeNeg
end
end
end
