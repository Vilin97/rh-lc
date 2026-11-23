module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantOrthogonalityHolds
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DividedPowerMonomialExpansion
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsHighestWeightVectorFindim
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightDominantHolds
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralGeneratorsPreserveLattice
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Interval
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorLatticeScaling
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint
import Mathlib.Tactic.Basify
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.MultidegreePartFinitelyGenerated

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def fockLattice {p : ℕ} (hV : ValuationProperties p O) (σ : Type) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {F | InBB (O := O) p F}
  zero_mem' := fock_lattice_zero_mem hV
  add_mem' := fun hF hG => fock_lattice_add_mem hV hF hG
  smul_mem' := fun o _ hF => fock_lattice_smul_mem hV o hF

theorem multidegree_monomials_finite {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) :
    {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin n => d x.1))).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  rintro ⟨i, c⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hm i]
  exact Finset.single_le_sum (f := fun c' => m (i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

theorem multidegree_part_finitely_generated {p : ℕ} (hp0 : (p : KK O) ≠ 0) {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) (N : ℕ)
    (h : ∀ F ∈ L, ∀ m, (∀ i, multideg m i = d i) → ∃ o : O, (p : KK O) ^ N * F.coeff m = algebraMap O (KK O) o) :
    (latticeMultidegreePart L d).FG := by
  classical
  set S := (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset with hS
  let f : ↥(Pol (KK O) n d) →ₗ[O] (S → KK O) :=
    { toFun := fun F s => (p : KK O) ^ N * (F : MvPolynomial (ι × Fin n) (KK O)).coeff s.1
      map_add' := fun F G => by
        funext s
        simp [mul_add]
      map_smul' := fun o F => by
        funext s
        simp [MvPolynomial.coeff_smul, mul_smul_comm] }
  let g : (S → O) →ₗ[O] (S → KK O) :=
    LinearMap.pi (fun s => (Algebra.linearMap O (KK O)).comp (LinearMap.proj s))
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro F hF
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_zero, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ S
    · have h0 := congrFun hF ⟨m, hm⟩
      change (p : KK O) ^ N * (F : MvPolynomial _ (KK O)).coeff m = 0 at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp0)
    · by_contra hne
      apply hm
      have hF2 : (F : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := F.2
      have hsupp : m ∈ (F : MvPolynomial _ (KK O)).support := MvPolynomial.mem_support_iff.2 hne
      exact (Set.Finite.mem_toFinset _).2 (((MvPolynomial.mem_restrictSupport_iff _).1 hF2) (Finset.mem_coe.2 hsupp))
  have hle : (latticeMultidegreePart L d).map f ≤ LinearMap.range g := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : MvPolynomial (ι × Fin n) (KK O)) ∈ L := hx
    choose o ho using fun s : S => h _ hx' s.1 ((Set.Finite.mem_toFinset _).1 s.2)
    refine ⟨o, ?_⟩
    funext s
    exact (ho s).symm
  have hW : (LinearMap.range g).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map g
  haveI : IsNoetherian O (LinearMap.range g) := isNoetherian_of_fg_of_noetherian _ hW
  have h1 : (((latticeMultidegreePart L d).map f).comap (LinearMap.range g).subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map (LinearMap.range g).subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2
  exact Submodule.fg_of_fg_map_injective f hinj h2

theorem multidegree_part_spans {ι : Type} [Fintype ι] {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ)
    (h : ∀ m, monomial m (1 : KK O) ∈ L) : MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro x -
  have hx : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
      MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i} := x.2
  have key : ∀ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support,
      monomial m (1 : KK O) ∈ Pol (KK O) n d := by
    intro m hm
    show monomial m (1 : KK O) ∈ MvPolynomial.restrictSupport (KK O) {m | ∀ i, multideg m i = d i}
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    rw [Finset.mem_coe] at hm'
    have hm'' := MvPolynomial.support_monomial_subset hm'
    rw [Finset.mem_singleton] at hm''
    subst hm''
    exact ((MvPolynomial.mem_restrictSupport_iff _).1 hx) (Finset.mem_coe.2 hm)
  have hx2 : x = ∑ m ∈ (x : MvPolynomial (ι × Fin n) (KK O)).support.attach,
      (x : MvPolynomial (ι × Fin n) (KK O)).coeff m.1 •
        (⟨monomial m.1 1, key m.1 m.2⟩ : Pol (KK O) n d) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [Finset.sum_attach _ (fun m => monomial m ((x : MvPolynomial (ι × Fin n) (KK O)).coeff m))]
    exact (x : MvPolynomial (ι × Fin n) (KK O)).as_sum
  rw [hx2]
  show _ ∈ Submodule.span (KK O) _
  refine Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact h m.1

theorem fock_lattice_finite_spanning_holds {p : ℕ} (hp : p.Prime) (S0 : UniformizedDVR p O) (hV : ValuationProperties p O) : FockLatticeFiniteSpanning p O := by
  intro n ι _
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    have h1 := hV.2.2.2.1 p hp.ne_zero
    rw [h0, hV.1] at h1
    exact WithTop.top_ne_coe h1
  have hv1 : vK p (1 : KK O) = 0 := by
    have h1 := hV.2.2.2.1 1 one_ne_zero
    rw [Nat.cast_one, Nat.padicValNat_def, multiplicity_one_right] at h1
    simpa using h1
  have key : ∀ (x : WithTop ℚ) (a b : ℚ), 0 ≤ x + (a : WithTop ℚ) → a ≤ b → 0 ≤ (b : WithTop ℚ) + x := by
    intro x a b hx hab
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe q =>
      rw [← WithTop.coe_add] at hx ⊢
      rw [WithTop.coe_nonneg] at hx ⊢
      linarith
  have hmono : ∀ m : ι × Fin n →₀ ℕ, monomial m (1 : KK O) ∈ fockLattice hV (ι × Fin n) := by
    intro m
    show InBB (O := O) p (monomial m (1 : KK O))
    rw [fock_lattice_monomial_iff hV, hv1, zero_add]
    unfold halfFactorialValuation
    exact WithTop.coe_nonneg.2 (by positivity)
  refine ⟨fockLattice hV (ι × Fin n), fun F => Iff.rfl, fun d => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact multidegree_part_finitely_generated hp0 _ d 0 (fun F hF m _ => by simpa using (mem_integral_poly_iff_coeff F).1 hF m)
  · exact multidegree_part_spans _ d (fun m => by simpa using integer_monomial_mem_integral (O := O) m 1)
  · refine multidegree_part_finitely_generated hp0 _ d
      (∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m)) ?_
    intro F hF m hm
    have hF' : InBB (O := O) p F := hF
    have h0 := (mem_fock_lattice_iff_coeff hV F).1 hF' m
    unfold halfFactorialValuation at h0
    apply (hV.2.2.2.2.2 _).1
    haveI := Fact.mk hp
    rw [hV.2.1, ← Nat.cast_pow, hV.2.2.2.1 _ (pow_ne_zero _ hp.ne_zero), Nat.padicValNat_def, Nat.multiplicity_prime_pow]
    refine key _ _ _ h0 ?_
    have hmS : m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset := (Set.Finite.mem_toFinset _).2 hm
    have hle := Finset.single_le_sum (f := fun m => padicValNat p (expFact m)) (fun _ _ => Nat.zero_le _) hmS
    have hle' : (padicValNat p (expFact m) : ℚ) ≤
        ((∑ m ∈ (multidegree_monomials_finite (ι := ι) (n := n) d).toFinset, padicValNat p (expFact m) : ℕ) : ℚ) := by
      exact_mod_cast hle
    have hnn : (0 : ℚ) ≤ padicValNat p (expFact m) := by positivity
    linarith
  · exact multidegree_part_spans _ d hmono

end Formalism.MainNotions.G.GLWeightTheory
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialIsotypicLatticeOfParts

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem operator_list_lattice_scaling {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p : ℕ)
    (L : Submodule O (MvPolynomial σ (KK O))) (W : Submodule (KK O) (MvPolynomial σ (KK O)))
    (l : List (Module.End (KK O) (MvPolynomial σ (KK O)) × ℕ))
    (hW : ∀ eD ∈ l, ∀ F ∈ W, eD.1 F ∈ W)
    (hL : ∀ eD ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ eD.2) • eD.1 F ∈ L) :
    ∀ F ∈ W, F ∈ L → (l.map Prod.fst).prod F ∈ W ∧
      ((p : KK O) ^ (l.map Prod.snd).sum) • (l.map Prod.fst).prod F ∈ L := by
  induction l with
  | nil =>
    intro F hF hFL
    simp [hF, hFL]
  | cons eD l ih =>
    intro F hF hFL
    have hW' : ∀ e ∈ l, ∀ F ∈ W, e.1 F ∈ W := fun e he => hW e (List.mem_cons_of_mem _ he)
    have hL' : ∀ e ∈ l, ∀ F ∈ W, F ∈ L → ((p : KK O) ^ e.2) • e.1 F ∈ L :=
      fun e he => hL e (List.mem_cons_of_mem _ he)
    obtain ⟨h1, h2⟩ := ih hW' hL' F hF hFL
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨hW eD (by simp) _ h1, ?_⟩
    have h3 := hL eD (by simp) _ (W.smul_mem ((p : KK O) ^ (l.map Prod.snd).sum) h1) h2
    rw [map_smul, smul_smul, ← pow_add] at h3
    exact h3

theorem polynomial_isotypic_lattice_of_parts (D : Formalism.BasicNotions.D7) (hCR : CompleteReducibilityIsotypic) (hOrth : ContravariantIsotypicOrthogonal) (hDom : HighestWeightDominant)
    (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (hLat : AdmissibleDVRIntegralFormLatticesStable) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D := by
  intro p n' O _ _ _ S0 hG n ι _ LL N Ss hmono
  obtain ⟨hchar, hLat'⟩ := hLat p n' O S0 hG
  obtain ⟨hL1, hL2, BBs, hBB, hL3⟩ := hLat' n ι LL
  refine ⟨fun i => hL1 (Ss i), ?_⟩
  intro ee hee
  obtain ⟨hP1, hP2, hP3, -, -, -, B, hB1, hB2⟩ := hPol (KK O) ι n LL
  have hT : ∀ S : Set ι, (⨆ mu : Fin n → ℤ, isoSub (glOps (KK O) n LL S) mu) = ⊤ :=
    fun S => hCR (KK O) _ n _ (hP1 S)

  have hdis : ∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
      ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam := by
    intro i lam S' hS' a b
    refine isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => ?_
    exact isotypic_stable_commuting _ _ (fun c d => (hP2 (Ss i) S' hS' c d a b).symm) mu x hx
  have hle : ∀ i j, i ≤ j → ∀ lam a b,
      ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam := by
    intro i j hij lam a b
    rw [hP3 (Ss i) (Ss j) (hmono hij) a b, mul_add, add_mul, hdis i lam _ Set.disjoint_sdiff_right a b]
    congr 1
    exact isotypic_projector_commutes _ (hT (Ss i)) lam _ (hee i lam) _ fun mu x hx => isotypic_stable_gl_operator _ mu a b x hx
  have hcomm' : ∀ i j, i ≤ j → ∀ lam mu, ee i lam * ee j mu = ee j mu * ee i lam := by
    intro i j hij lam mu
    refine (isotypic_projector_commutes _ (hT (Ss j)) mu _ (hee j mu) _ fun nu x hx => ?_).symm
    exact isotypic_stable_commuting _ _ (fun c d => hle i j hij lam c d) nu x hx
  refine ⟨hle, hdis, ?_, ?_, ?_⟩
  · intro i j lam mu
    rcases le_total i j with h | h
    · exact hcomm' i j h lam mu
    · exact (hcomm' j i h mu lam).symm
  · intro i lam F G
    rw [← hB1, ← hB1]
    exact isotypic_projector_selfAdjoint _ (hT (Ss i)) lam _ (hee i lam) B
      (hOrth (KK O) _ n _ (hP1 (Ss i)) B (fun a b x y => hB2 (Ss i) a b x y)) F G
  · intro T d F hF
    have hstep := fun (i : Fin N) (lam : Fin n → ℤ) =>
      isotypic_projector_lattice_scaling D hDom hRes hPol h13 p n' O S0 hG n ι LL (Ss i) d lam (ee i lam) (hee i lam)
    have main : ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
        (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
        MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ → F ∈ L →
        ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
          (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ L := by
      intro L hst hFG hMQ hFL
      rw [LinearMap.sum_apply, Finset.smul_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      have h := operator_list_lattice_scaling p L (Pol (KK O) n d)
        (List.ofFn fun i => (ee i (t i), N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1)))
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).1)
        (by
          intro eD heD
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 heD
          exact (hstep i (t i)).2 L (hst (Ss i)) hFG hMQ) F hF hFL
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h.2
    obtain ⟨h1, h2, h3, h4⟩ := hL3 d
    refine ⟨fun hFL => main _ (fun S u hu => (hL2 S u hu).1) h1 h2 hFL, fun hFB => ?_⟩
    rw [← hBB] at hFB ⊢
    exact main BBs (fun S u hu F hF => (hBB _).2 ((hL2 S u hu).2 F ((hBB _).1 hF))) h3 h4 hFB

end Formalism.MainNotions.G.GLWeightTheory
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolynomialsEnvelopingStable

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem integral_formula_lattice_holds : AdmissibleDVRIntegralFormLatticesStable := by
  intro p n' O _ _ _ S0 hG
  have hV : ValuationProperties p O := valuation_properties_hold hG.prime S0
  have hchar := dvr_fraction_field_char_zero hG.prime S0
  exact ⟨hchar, fun n ι _ LL => ⟨fun S => integral_formula_stability_holds hG.prime hV n ι LL S,
    fun S => char_zero_stability_of_closure hG.prime hchar (fock_lattice_closure_holds hV) n ι LL S, fock_lattice_finite_spanning_holds hG.prime S0 hV n ι⟩⟩

theorem polynomial_isotypic_lattice_corollary (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h13 : IsotypicProjectorTheoremField D) : FilteredProjectorCorollaryField D :=
  polynomial_isotypic_lattice_of_parts D (complete_reducibility_of_semisimple D h2) contravariant_orthogonality_holds highest_weight_dominant_holds (subrep_restriction_of_reducibility (complete_reducibility_of_semisimple D h2)) polynomial_representation_holds integral_formula_lattice_holds h13

end Formalism.MainNotions.G.GLWeightTheory
end
end
end
