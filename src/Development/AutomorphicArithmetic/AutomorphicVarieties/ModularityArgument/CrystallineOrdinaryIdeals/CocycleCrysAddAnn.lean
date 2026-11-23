module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankCocyclesEqCrysAddDualInvOfPositiveStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.PositiveScalarRepOfCharacterPositiveWeightStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositive

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.cocycle_eq_crys_add_sub : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ W _ _ _ _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρW ρ hcW hc hpW hp i hi hiρ hdim c hcZ
  obtain ⟨hfinW, hdW⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρW hcW hpW
  obtain ⟨hfin, hd⟩ := GlobalTheory.T.finrank_cocycles_eq_crys_add_dual_inv_of_positive hP φ hφ ρ hc hp
  have hic : Continuous i := IsModuleTopology.continuous_of_linearMap (i.restrictScalars ℚ_[l])
  let S := (finiteCocycles φ ρ).comap (Z1 ρ).subtype
  let SW := (finiteCocycles φ ρW).comap (Z1 ρW).subtype
  let M : Z1 ρW →ₗ[E] Z1 ρ := LinearMap.codRestrict (Z1 ρ) ((LinearMap.compLeft i G).comp (Z1 ρW).subtype)
    (fun c' => ⟨hic.comp c'.2.1, fun g h => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.compLeft_apply, Function.comp_apply,
        c'.2.2 g h, map_add, hiρ]⟩)
  have hM : ∀ c' g, ((M c' : Z1 ρ) : G → V) g = i ((c' : G → W) g) := fun _ _ => rfl
  let L : Z1 ρW →ₗ[E] Z1 ρ ⧸ S := S.mkQ ∘ₗ M
  have hker : LinearMap.ker L = SW := by
    ext c'
    simp only [L, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, SW, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      exact (posExact hP φ hφ ρW ρ hcW hc hpW i hiρ).2 hi hp _ c'.2 h
    · intro h
      exact (z1fMap φ ρW ρ).2 (i.restrictScalars ℚ_[l]) (fun g x => hiρ g x) _ h
  have eW : SW ≃ₗ[E] finiteCocycles φ ρW := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have eV : S ≃ₗ[E] finiteCocycles φ ρ := Submodule.comapSubtypeEquivOfLe (fun x hx => hx.1)
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_quotient_add_finrank S
  rw [hker, eW.finrank_eq] at h1
  rw [eV.finrank_eq] at h2
  have hr : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨c', hc'⟩ : S.mkQ ⟨c, hcZ⟩ ∈ LinearMap.range L := hr ▸ Submodule.mem_top
  refine ⟨c', c'.2, ?_⟩
  have := (Submodule.Quotient.eq S).1 hc'.symm
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub] at this
  exact this
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleMemCrystallineSupSubrepOfPositiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {W : Type} [AddCommGroup W] [Module E W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] E W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul E W] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρW : Representation E G W) (ρ : Representation E G V), ContAction ρW → ContAction ρ → Positive φ ρW → Positive φ ρ → ∀ i : W →ₗ[E] V, Function.Injective i → (∀ g x, i (ρW g x) = ρ g (i x)) → finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρ) → ∀ c ∈ Z1 ρ, ∃ c' ∈ Z1 ρW, (c - fun g => i (c' g)) ∈ finiteCocycles φ ρ := by
  first | exact @GlobalTheory.cocycle_eq_crys_add_sub | exact GlobalTheory.cocycle_eq_crys_add_sub | (intros; apply GlobalTheory.cocycle_eq_crys_add_sub <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankDualInvariantsScalarRepEqFinrankKerSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul : ∀ {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N] (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ∀ δ : B, Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ} → finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  intro G E B _ _ _ _ _ N _ _ _ _ _ χ ε ρ hρ δ hδ
  set L := (LinearMap.lsmul B N δ).restrictScalars E with hL
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    have hmem : f ∈ H0dual ε ρ ↔ ∀ (g : G) (x : N), f (ρ g x) = (ε g : E) * f x := by
      unfold H0dual
      exact Iff.rfl
    rw [hmem, Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun {a b} ha hb x => by
          simp only [Set.mem_setOf_eq] at ha hb
          rw [add_smul, map_add (f := _), ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by
          simp only [Set.mem_setOf_eq] at hb
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb _ }
    have hS : ∀ b, b ∈ S ↔ ∀ x : N, f (b • x) = 0 := fun b => Iff.rfl
    have hgen : ∀ g, (∀ x, f (ρ g x) = (ε g : E) * f x) ↔
        ((χ g : B) - algebraMap E B (ε g)) ∈ S := by
      intro g
      rw [hS]
      refine forall_congr' fun x => ?_
      rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul (ε g : E) x, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        exact (hgen g).1 (h g)
      rw [hδ] at hle
      have hd : δ ∈ S := hle (Ideal.subset_span rfl)
      rintro _ ⟨x, rfl⟩
      exact hd x
    · intro h g
      rw [hgen]
      have hd : δ ∈ S := fun x => h _ ⟨x, rfl⟩
      have hle : Ideal.span {δ} ≤ S := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hd
      rw [← hδ] at hle
      exact hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeight

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CharCycIdeal

theorem isClosed_ideal {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] (J : Ideal B) : IsClosed (J : Set B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  refine Filter.mem_of_superset ((isOpen_ne.preimage hc).mem_nhds (x := x) hf) fun y hy h => hy ?_
  exact hJ (x := y) h

theorem span_range_sub_cyc : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχ w hw hI σ hσ
  have hA : ∀ g : GQ l, (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g =>
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  split_ifs with h1
  · subst h1
    refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
    set J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} with hJ
    have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
      simp only [hA]
      have h0 : Continuous (algebraMap ℚ_[l] B) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)
      have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
      exact h0.comp (h2.comp (Units.continuous_val.comp
        ((UpperTheory.V.Loc.cycFacts l l).1.comp hφ.continuous)))
    let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
    let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
    have hH : ∀ g, g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := fun g => by
      rw [← Ideal.Quotient.eq]
      exact Units.ext_iff
    have hcl : IsClosed (H : Set G) := by
      have : (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) := Set.ext hH
      rw [this]
      exact (isClosed_ideal (l := l) J).preimage (hχ.sub hε)
    have hle : (Iq l).comap φ ⊔ Subgroup.zpowers σ ≤ H := by
      refine sup_le (fun g hg => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [hH, hI g hg, zpow_one, sub_self]
        exact J.zero_mem
      · rw [hH]
        exact Ideal.subset_span rfl
    have htop := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hσ] at htop
    rw [Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact (hH g).1 (htop (Subgroup.mem_top g))
  · obtain ⟨s, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((UpperTheory.V.Loc.cycInertia l).2 φ.range hφ.isOpen_range).2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
    show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
    rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val, hA, ← map_pow, ← map_sub]
    refine IsUnit.map _ (Ne.isUnit fun h => hs ?_)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩
    have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := by
      apply Units.ext
      apply Subtype.ext
      rw [Units.val_pow_eq_pow_val]
      push_cast
      exact sub_eq_zero.1 h
    rw [pow_succ] at h2
    exact mul_eq_right.1 h2

end GlobalTheory.CharCycIdeal
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeightStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  first | exact @GlobalTheory.CharCycIdeal.span_range_sub_cyc | exact GlobalTheory.CharCycIdeal.span_range_sub_cyc | (intros; apply GlobalTheory.CharCycIdeal.span_range_sub_cyc <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CocycleCrysAddAnn

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology TensorProduct

noncomputable section
namespace GlobalTheory.CrysAnn

variable {l : ℕ} [Fact l.Prime]

theorem actC_resCoef {G E B : Type} [Group G] [Field E] [Algebra ℚ_[l] E] [CommRing B] [Algebra ℚ_[l] B]
    [Algebra E B] [IsScalarTower ℚ_[l] E B] (φ : G →* GQ l) (ρ : Representation B G B) (g : G)
    (y : B ⊗[ℚ_[l]] Bcr l) : actC φ (resCoef E ρ) g y = actC φ ρ g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [actC, resCoef]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

def smulRep {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] (N : Type) [AddCommGroup N]
    [Module B N] [Module E N] [IsScalarTower E B N] (χ : G →* Bˣ) : Representation E G N where
  toFun g := (LinearMap.lsmul B N (χ g : B)).restrictScalars E
  map_one' := by ext; simp
  map_mul' g h := by
    ext x
    simp [mul_smul]
    exact smul_comm _ _ _

end GlobalTheory.CrysAnn


open GlobalTheory.CrysAnn in
theorem GlobalTheory.CrysAnn.cocycle_crys_add_ann : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → ∀ c ∈ Z1 (chRep χ), ∃ c' : G → B, (∀ g, ((χ σ : B) - (cycA l l B (φ σ) : B)) * c' g = 0) ∧ c - c' ∈ finiteCocycles φ (chRep χ) ∧ (2 ≤ w → c' = 0) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχc w hw hχI σ hσ c hc
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  set δ : B := if w = 1 then (χ σ : B) - (cycA l l B (φ σ) : B) else 1 with hδ
  have hspan : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E)) =
      Ideal.span {δ} := by
    have h := GlobalTheory.T.span_character_sub_cyclotomic_eq_of_positive_weight φ hφ π hπ χ hχc w hw hχI σ hσ
    have e : ∀ g, algebraMap E B (((cycA l l E).comp φ g : Eˣ) : E) = (cycA l l B (φ g) : B) := fun g =>
      congrArg Units.val (algebraMap_cycA (E := E) (B := B) (φ g))
    simp only [e, h, hδ]
    split_ifs <;> simp
  let I : Submodule B B := LinearMap.ker (LinearMap.lsmul B B δ)
  letI : TopologicalSpace I := moduleTopology ℚ_[l] I
  haveI : IsModuleTopology ℚ_[l] I := ⟨rfl⟩
  haveI : IsTopologicalAddGroup I := IsModuleTopology.topologicalAddGroup ℚ_[l] I
  haveI : ContinuousConstSMul E I := ⟨fun a => IsModuleTopology.continuous_of_linearMap
    ((LinearMap.lsmul E I a).restrictScalars ℚ_[l])⟩
  haveI : FiniteDimensional ℚ_[l] I :=
    Module.Finite.of_injective (I.subtype.restrictScalars ℚ_[l]) Subtype.val_injective
  let ρV : Representation E G B := resCoef E (chRep χ)
  let ρW : Representation E G I := smulRep I χ
  have hV := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρV (fun g x => rfl)
  have hW := GlobalTheory.T.positive_scalar_rep_of_character_positive_weight φ hφ π hπ χ hχc w hw hχI ρW (fun g x => rfl)
  have dV := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρV (fun g x => rfl) δ hspan
  have dW := GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul χ ((cycA l l E).comp φ) ρW (fun g x => rfl) δ hspan
  have kW : LinearMap.ker ((LinearMap.lsmul B I δ).restrictScalars E) = ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subtype.ext x.2
  have hdim : finrank E ↥(H0dual ((cycA l l E).comp φ) ρW) = finrank E ↥(H0dual ((cycA l l E).comp φ) ρV) := by
    rw [dV, dW, kW, finrank_top]
    exact (LinearEquiv.refl E I).finrank_eq
  let i : I →ₗ[E] B := I.subtype.restrictScalars E
  obtain ⟨cW, -, hf⟩ := GlobalTheory.T.cocycle_mem_crystalline_sup_subrep_of_positive hP φ hφ ρW ρV hW.1 hV.1 hW.2 hV.2 i Subtype.val_injective
    (fun g x => rfl) hdim c hc
  have hz : w ≠ 1 → ∀ g, (cW g : B) = 0 := by
    intro h1 g
    have := (cW g).2
    simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_neg h1, one_smul] at this
    exact this
  refine ⟨fun g => (cW g : B), fun g => ?_, ?_, fun h2 => funext fun g => hz (by omega) g⟩
  · by_cases h1 : w = 1
    · have := (cW g).2
      simp only [I, LinearMap.mem_ker, LinearMap.lsmul_apply, hδ, if_pos h1, smul_eq_mul] at this
      exact this
    · show _ * (cW g : B) = 0
      rw [hz h1 g, mul_zero]
  · obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hf
    exact ⟨⟨hc1, hc2⟩, x, fun g => (hx g).trans (by rw [actC_resCoef])⟩
end
end
end
