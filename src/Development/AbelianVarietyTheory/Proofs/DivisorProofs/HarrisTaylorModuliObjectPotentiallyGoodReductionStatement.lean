module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffHasMultiplicities
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem eq_zero_of_mem_eigenSub_of_sum {O k N : Type} [CommRing O] [Field k] [AddCommGroup N] [Module k N]
    (ρ : O →+* Module.End k N) (σ : O →+* k) {κ : Type} (χ : κ → O →+* k) (hχ : ∀ i, χ i ≠ σ)
    (s : Finset κ) : ∀ (m : N) (y : κ → N), m ∈ eigenSub ρ σ → (∀ i, y i ∈ eigenSub ρ (χ i)) →
      m = ∑ i ∈ s, y i → m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m y _ _ h; simpa using h
  | insert j s hj ih =>
    intro m y hm hy h
    obtain ⟨c, hc⟩ : ∃ c, χ j c ≠ σ c := by
      by_contra hcon
      push_neg at hcon
      exact hχ j (RingHom.ext hcon)
    let f : Module.End k N := ρ c - χ j c • LinearMap.id
    have hfm : f m = (σ c - χ j c) • m := by
      simp [f, mem_eigenSub.1 hm c, sub_smul]
    have hfy : ∀ i, f (y i) = (χ i c - χ j c) • y i := fun i => by
      simp [f, mem_eigenSub.1 (hy i) c, sub_smul]
    have h1 : (σ c - χ j c) • m = ∑ i ∈ s, (χ i c - χ j c) • y i := by

      rw [← hfm, h, Finset.sum_insert hj, map_add (f := _), map_sum, hfy j, sub_self, zero_smul, zero_add]
      exact Finset.sum_congr rfl fun i _ => hfy i
    have h2 := ih ((σ c - χ j c) • m) (fun i => (χ i c - χ j c) • y i)
      (Submodule.smul_mem _ _ hm) (fun i => Submodule.smul_mem _ _ (hy i)) h1
    have hne : σ c - χ j c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    exact (smul_eq_zero.1 h2).resolve_left hne

theorem exists_ringHom_avoid {F : Type} [Field F] [NumberField F] [IsCMField F] (bar : 𝓞 F ≃+* 𝓞 F)
    (bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F))
    (ω : 𝓞 F) (tr nm : ℤ) (tr_eq : ω + bar ω = (tr : 𝓞 F)) (nm_eq : ω * bar ω = (nm : 𝓞 F))
    (disc_neg : tr ^ 2 - 4 * nm < 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (ρ : k) (hρ : ρ ^ 2 - tr * ρ + nm = 0)
    (a : ℕ) (ha : 2 * a < Module.finrank ℚ F) (χ : Fin a → (𝓞 F →+* k)) :
    ∃ σ : 𝓞 F →+* k, σ ω = ρ ∧ ∀ i, χ i ≠ σ := by
  classical
  let cj : F →+* F := ((IsCMField.complexConj F : F ≃ₐ[maximalRealSubfield F] F) : F →+* F)
  have e1 : (ω : F) + ((bar ω : 𝓞 F) : F) = (tr : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) tr_eq
    simpa using this
  have e2 : (ω : F) * ((bar ω : 𝓞 F) : F) = (nm : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) nm_eq
    simpa using this
  have hcω : cj (ω : F) = (tr : F) - (ω : F) := by
    have : cj (ω : F) = ((bar ω : 𝓞 F) : F) := (bar_eq ω).symm
    rw [this]; linear_combination e1
  have hcc : ∀ z, cj (cj z) = z := fun z => IsCMField.complexConj_apply_apply F z
  have hroot : ∀ τ : F →+* k, τ ω ^ 2 - tr * τ ω + nm = 0 := by
    intro τ
    have h1 : (ω : F) ^ 2 - tr * (ω : F) + nm = 0 := by
      linear_combination (ω : F) * e1 - e2
    have := congrArg τ h1
    simpa using this
  have hne : ρ ≠ (tr : k) - ρ := by
    intro h
    have h3 : ((tr ^ 2 - 4 * nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * ρ - tr) * h - 4 * hρ
    have h4 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h3
    omega
  have hside : ∀ τ : F →+* k, τ ω ≠ ρ → τ ω = (tr : k) - ρ := by
    intro τ h
    have : (τ ω - ρ) * (τ ω - ((tr : k) - ρ)) = 0 := by
      linear_combination hroot τ - hρ
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h') h
    · exact sub_eq_zero.1 h'
  have hconj : ∀ τ : F →+* k, (τ.comp cj) ω = (tr : k) - τ ω := by
    intro τ
    simp [hcω]
  let T := (Finset.univ : Finset (F →+* k)).filter (fun τ => τ ω = ρ)
  let Tc := (Finset.univ : Finset (F →+* k)).filter (fun τ => ¬ τ ω = ρ)
  have hcard : T.card = Tc.card := by
    refine Finset.card_nbij' (fun τ => τ.comp cj) (fun τ => τ.comp cj) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hτ]
      exact fun h => hne h.symm
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hside τ hτ]; ring
    · intro τ _; ext z; simp [hcc]
    · intro τ _; ext z; simp [hcc]
  have htot : T.card + Tc.card = Module.finrank ℚ F := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, NumberField.Embeddings.card]
  by_contra hcon
  push_neg at hcon
  have hsub : T.image (fun τ => τ.comp (algebraMap (𝓞 F) F)) ⊆ Finset.univ.image χ := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨i, hi⟩ := hcon (τ.comp (algebraMap (𝓞 F) F)) (by simpa using hτ)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hinj : Set.InjOn (fun τ : F →+* k => τ.comp (algebraMap (𝓞 F) F)) T := by
    intro τ _ τ' _ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hle
  have hle2 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin a))) (f := χ))
  rw [Finset.card_univ, Fintype.card_fin] at hle2
  omega

end GlobalTheory.HTLie

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem exists_lieMult_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  intro p _ D R _ b N S s o ha k _ _ _ x β hx
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  obtain ⟨σ, hσω, hσ⟩ := exists_ringHom_avoid D.bar D.bar_eq D.ω D.tr D.nm D.tr_eq D.nm_eq D.disc_neg k
    (β b.ρ) hρ D.a ha (fun i => β.comp (b.t i))
  refine ⟨σ, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun w hw =>
    ⟨Fin.elim0, ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩, fun c _ => funext fun i => Fin.elim0 i⟩⟩
  rw [List.ofFn_zero, List.prod_nil]
  obtain ⟨w', hw', hwprod⟩ := o.lie k β x hx w ⟨hw.1, by
    have := hw.2 D.ω
    rw [hσω] at this
    exact this⟩
  have hlie : ∀ i, IsLieEigen (o.act.toF D) x (β.comp (b.t i)) (w' i) :=
    fun i => ⟨(hw' i 0).1, fun c => (hw' i c).2⟩
  obtain ⟨h1, h2⟩ := (isLieEigen_iff _ x σ w).1 hw
  choose g1 g2 using fun i => (isLieEigen_iff _ x _ (w' i)).1 (hlie i)
  have hm := (mem_eigenspace_iff _ x σ _).1 h2
  have hy := fun i => (mem_eigenspace_iff _ x _ _).1 (g2 i)
  have hsum : lieEquiv x ⟨w, h1⟩ = ∑ i ∈ Finset.univ, lieEquiv x ⟨w' i, g1 i⟩ := by
    apply TanSp.ext
    rw [TanSp.pt_sum]
    show w = ∏ i, w' i
    rw [hwprod, List.prod_ofFn]
  have h0 := eq_zero_of_mem_eigenSub_of_sum _ σ (fun i => β.comp (b.t i)) hσ Finset.univ _ _ hm hy hsum
  exact congrArg TanSp.pt h0

end GlobalTheory.HTLie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZeroStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  first | exact @GlobalTheory.HTLie.exists_lieMult_zero | exact GlobalTheory.HTLie.exists_lieMult_zero | (intros; apply GlobalTheory.HTLie.exists_lieMult_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLattice

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLatticeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.two_mul_relDim_eq_finrank_harrisTaylor_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  first | exact @GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank | exact GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank | (intros; apply GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReduction

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTPotGood

theorem potGood : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro p _ D R _ b N V K _ _ _ _ _ _ _ _ β o h
  rcases h with h | ⟨hdiv, hn⟩
  · let Ω := AlgebraicClosure K
    have hx : spMap (algebraMap K Ω) ≫ spMap β = spMap ((algebraMap K Ω).comp β) := by
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero p D R b N (Sp K) (spMap β) o h Ω (spMap (algebraMap K Ω))
      ((algebraMap K Ω).comp β) hx
    exact GlobalTheory.T.potentialGoodReduction_of_lieMult_zero V K o.A o.ab D.F (o.act.toF D) Ω (algebraMap K Ω) σ hσ
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K o.A o.ab
    have h2g := GlobalTheory.T.two_mul_relDim_eq_finrank_harrisTaylor_lattice p D R b N K β o g hg
    rw [D.rankLa] at h2g
    haveI := D.freeO
    haveI := D.finO
    have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    have hm := D.m_pos
    have hlt : g < Module.finrank ℤ D.O := by
      rw [D.rankO]
      have h1 : D.m * D.n * Module.finrank ℚ D.F < D.m * (2 * D.m) * Module.finrank ℚ D.F := by
        apply Nat.mul_lt_mul_of_pos_right _ hd
        exact Nat.mul_lt_mul_of_pos_left hn hm
      have h2 : D.m * (2 * D.m) * Module.finrank ℚ D.F = 2 * (D.m ^ 2 * Module.finrank ℚ D.F) := by ring
      omega
    exact GlobalTheory.T.potentialGoodReduction_of_order_leftAction V K o.A g o.ab hg D.O o.act.act o.act.hom o.act.one o.act.mul o.act.add hdiv hlt

end GlobalTheory.HTPotGood
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReductionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.HTPotGood.potGood | exact GlobalTheory.HTPotGood.potGood | (intros; apply GlobalTheory.HTPotGood.potGood <;> assumption)
end
end
