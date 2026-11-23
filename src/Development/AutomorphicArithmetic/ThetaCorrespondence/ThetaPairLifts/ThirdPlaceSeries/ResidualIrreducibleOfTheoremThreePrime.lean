module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.CyclotomicNorms.StatementI
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.RestrictionOfBlocksAndJordan
public import Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.CyclotomicNorms.NonsquarefreeBounds.Jordan

section

@[expose] public section

open Finset

namespace Formalism.CyclotomicNorms

theorem blocks_form_cycle : BlocksCycle := by
  unfold BlocksCycle
  intro G Ω _ _ _ _ B m p g₀ hsize hdisj hcover hinv hp hlt hcyc hsupp
  have hpow : ∀ (i : ℕ) (y : Ω), ((MulAction.toPerm g₀ : Equiv.Perm Ω) ^ i) y = g₀ ^ i • y := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; simp [pow_succ, mul_smul, ih]
  have hord : orderOf (MulAction.toPerm g₀ : Equiv.Perm Ω) = p := by
    rw [hcyc.orderOf, hsupp]
  have hfix : ∀ y : Ω, g₀ ^ p • y = y := by
    intro y
    have h1 := pow_orderOf_eq_one (MulAction.toPerm g₀ : Equiv.Perm Ω)
    rw [hord] at h1
    rw [← hpow]
    simp [h1]
  obtain ⟨φ, hφdef⟩ : ∃ φ : Finset Ω → Finset Ω, ∀ s, φ s = s.image (fun x => g₀ • x) :=
    ⟨fun s => s.image (fun x => g₀ • x), fun _ => rfl⟩
  have hφ : ∀ (i : ℕ) (s : Finset Ω), φ^[i] s = s.image (fun x => g₀ ^ i • x) := by
    intro i
    induction i with
    | zero => intro s; simp
    | succ i ih =>
      intro s
      rw [Function.iterate_succ_apply', ih, hφdef, Finset.image_image]
      congr 1
      funext x
      dsimp [Function.comp_apply]
      rw [← mul_smul, ← pow_succ']
  have hφB : ∀ (i : ℕ), ∀ s ∈ B, φ^[i] s ∈ B := by
    intro i s hs
    rw [hφ]
    exact hinv (g₀ ^ i) s hs
  have hper : ∀ s : Finset Ω, φ^[p] s = s := by
    intro s
    rw [hφ]
    simp [hfix]
  have hp2 := hp.two_le
  obtain ⟨x, hx⟩ : (MulAction.toPerm g₀ : Equiv.Perm Ω).support.Nonempty := by
    rw [← Finset.card_pos, hsupp]
    omega
  obtain ⟨b, hbB, hxb⟩ := hcover x
  have hcard : Fintype.card Ω = B.card * m := by
    have hU : B.biUnion (fun c => c) = Finset.univ := by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      obtain ⟨c, hc, hyc⟩ := hcover y
      exact ⟨c, hc, hyc⟩
    rw [← Finset.card_univ, ← hU, Finset.card_biUnion (fun c hc c' hc' hne => hdisj c hc c' hc' hne)]
    exact Finset.sum_const_nat hsize
  have hmp : Function.minimalPeriod φ b ∣ p :=
    Function.IsPeriodicPt.minimalPeriod_dvd (hper b)
  rcases (Nat.dvd_prime hp).1 hmp with h1 | hpp
  · left
    have hfixb : φ b = b := Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
    have hsub : (MulAction.toPerm g₀ : Equiv.Perm Ω).support ⊆ b := by
      intro y hy
      obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx) (Equiv.Perm.mem_support.1 hy)
      have hib : φ^[i] b = b := Function.iterate_fixed hfixb i
      rw [← hi, hpow, ← hib, hφ]
      exact Finset.mem_image_of_mem _ hxb
    have hpm : p ≤ m := by
      rw [← hsupp, ← hsize b hbB]
      exact Finset.card_le_card hsub
    have hk1 : 1 ≤ B.card := Finset.card_pos.2 ⟨b, hbB⟩
    by_contra hne
    have hk2 : 2 ≤ B.card := by omega
    have h2 := Nat.mul_le_mul hk2 hpm
    linarith
  · right
    have hinj : Set.InjOn (fun n => φ^[n] b) (Finset.range p : Set ℕ) := by
      rw [Finset.coe_range, ← hpp]
      exact Function.iterate_injOn_Iio_minimalPeriod
    have hkp : p ≤ B.card := by
      have h1 : ((Finset.range p).image (fun n => φ^[n] b)) ⊆ B := by
        intro c hc
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hc
        exact hφB n b hbB
      have h2 := Finset.card_le_card h1
      rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at h2
    have hm1 : 1 ≤ m := by
      rw [← hsize b hbB]
      exact Finset.card_pos.2 ⟨x, hxb⟩
    have hm : m = 1 := by
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have h3 := Nat.mul_le_mul hkp hm2
      linarith
    rw [hcard, hm, mul_one]

theorem jordan_transitivity : JordanTransitive := by
  intro G Ω _ _ _ _ p g₀ htr hp hlt hle hcyc hsupp
  set K : Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom G Ω).range with hK
  set σ : Equiv.Perm Ω := MulAction.toPerm g₀ with hσ
  have hσK : σ ∈ K := ⟨g₀, rfl⟩
  have htrK : MulAction.IsPretransitive K Ω := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := htr.exists_smul_eq x y
    exact ⟨⟨MulAction.toPermHom G Ω g, ⟨g, rfl⟩⟩, hg⟩
  have hprim : MulAction.IsPreprimitive K Ω :=
    Formalism.GaloisIrreducibility.primitiveOfPCycle Ω K σ p hp hσK hcyc hsupp hlt htrK
  have halt : alternatingGroup Ω ≤ K :=
    Formalism.GaloisIrreducibility.jordanPrime Ω K σ p hp hσK hcyc hsupp hle hprim
  refine ⟨halt, ?_⟩
  have hpc : p ∈ σ.cycleType := by
    rw [hcyc.cycleType, hsupp]
    simp
  have hns : ¬ Group.IsSolvable K :=
    Formalism.GaloisIrreducibility.noSolvableTransitive Ω K σ p hp hσK hpc hlt hle htrK
  intro hG
  exact hns (Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (MulAction.toPermHom G Ω)))

end Formalism.CyclotomicNorms
end
end

-- Source module: Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple

section

@[expose] public section

namespace Formalism.CyclotomicNorms

theorem restriction : Restriction := restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity

theorem irreducibility_of_good_tuple : IrreducibilityCriterion := irreducibility_of_restriction restriction

end Formalism.CyclotomicNorms
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TheoremThreePrimeHolds

section

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem theorem_three_prime_holds_alt_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleThreePrime.ThreePrimeTheoremStatement D := by
  rintro ⟨hT, hG⟩ hBB i Sig ⟨x, hx⟩ hdz hgood
  have hcusp := cusp_of D hT i x Sig hx hgood
  refine ⟨hcusp, fun ρ hρ => ?_⟩
  have hG' := _root_.UpperTheory.GalS.g3p' hG i Sig ⟨x, hx⟩ hdz (fun k v => (hgood k).1.2.1 v) hcusp ρ hρ
  have hfact : ∀ j : Fin 2, Fact (D.host.g j).Prime := fun j => ⟨D.host.g_prime j⟩
  have hBB' : Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hBB
  have hne : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → D.nd.l i ≠ D.host.g k :=
    fun k hk h => hk (Or.inl h)
  have key : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn (redF D i ρ) ⊤ ∧
      (∀ (H : Subgroup (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) [H.Normal], Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) →
        Group.IsSolvable (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ H) → (∀ v, D.ntypes.tg k v ∈ H) →
        Formalism.CyclotomicNorms.IrredOn (redF D i ρ) H) := by
    intro k hk
    have hA := (hG' k (hne k hk)).1
    choose ι hι using hA
    choose φ hφ using fun v => (hι v).2.2
    have T := Formalism.CyclotomicNorms.irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
      (fun j v => D.naut.items₂ j (D.naut.plGw j v) (isoLoc D.nd D.naut Sig (D.naut.plGw j v)))
      D.nd.chiT hBB' (fun j => (hgood j).1) (D.nd.l i) k hk (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (redF D i ρ)
      (fun v => D.ntypes.tg k v) φ ι hφ (fun v => (hι v).1) (fun v => (hι v).2.1)
    exact ⟨T.1, T.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)
    · have h1 : D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := fun h1 => by
        have hm : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := ⟨h0, h1⟩
        rw [hBB'] at hm
        exact hm
      exact (key 1 h1).1
    · exact (key 0 h0).1
  · intro k hk Hs _ hopen hsolv hIne
    have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ Hs) := Subgroup.quotient_finite_of_isOpen Hs hopen
    exact (key k hk).2 Hs inferInstance hsolv
      (fun v => hIne _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))
  · intro k hk w hw hTG
    obtain ⟨v, j, ι, e₁, e₂, he₁, he₂, hinj, hcp, hchi⟩ := (hG' k hk).2 w hw hTG
    show ¬ (Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)))).IsRoot _
    rw [hcp, hchi]
    exact not_root_of hk (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
      (D.nd.chiT k) (hgood k).1 (hgood k).2 v j ι hinj e₁ e₂ he₁ he₂
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualIrreducibleOfTheoremThreePrime

section

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.AdmissibleThreePrime
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
theorem residual_irreducible_of_theorem_three_prime_alt (D : D7) (h : _root_.Formalism.MainNotions.AdmissibleThreePrime.Adm3PVariant D) (hAN : SumRepresentations.adm5 D) (hBN : LitBNIrr (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))
    (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) : ResidualIrreducibleRankR D :=
  residual_irreducible_of_theorem D (_root_.Formalism.MainNotions.AdmissibleThreePrime.theorem_three_prime_holds_alt_alt D h) hAN hBN hrho hdz
end Formalism.MainNotions.AdmissibleThreePrime
end
end
end
end
