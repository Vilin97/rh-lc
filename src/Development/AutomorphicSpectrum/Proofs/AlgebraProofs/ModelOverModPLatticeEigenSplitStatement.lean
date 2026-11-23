module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleProductStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersectionStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeCharacterStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticePermutedStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBound

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelSeq

section Lattices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat (R : Subalgebra o Ω) {κ : Type} (v : κ → Ω) :
    v ∈ stdLat R κ ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem af_le_std (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af R p χ ≤ stdLat R (Fin n) := by
  have hl1 : D.l1 R p ≤ stdLat R _ := by
    refine sup_le hB.M_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (mem_stdLat R _).2 fun i => ?_
    have := (mem_stdLat R f).1 hf i
    simpa using R.mul_mem (natCast_mem R p) this
  intro l hl
  refine (mem_stdLat R l).2 fun i => ?_
  have h := (mem_stdLat R _).1 (hl1 hl) (Pi.single i 1)
  have e : (linMap n χ) l (Pi.single i 1) = l i := by
    simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  have e' : (linMap n χ).toAddMonoidHom l (Pi.single i 1) = l i := e
  rwa [e'] at h

theorem std_le_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : stdLat R (Fin n) ≤ D.hh R p χ := by
  intro v hv
  refine (mem_dotDual R _ v).2 fun l hl => ?_
  have hl' := (mem_stdLat R l).1 (af_le_std D R p w hB χ h0 h1 hl)
  have hv' := (mem_stdLat R v).1 hv
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std_of_mem_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (h : mulLat w (stdLat R _) ≤ D.af R p χ) {b : Fin n → Ω} (hb : b ∈ D.hh R p χ) :
    w • b ∈ stdLat R (Fin n) := by
  refine (mem_stdLat R _).2 fun i => ?_
  have hi : (Pi.single i 1 : Fin n → Ω) ∈ stdLat R (Fin n) := by
    refine (mem_stdLat R _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp [one_mem]
    · simp [Pi.single_eq_of_ne hj, zero_mem]
  have hm : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p χ := h ⟨_, hi, rfl⟩
  have := (mem_dotDual R _ b).1 hb _ hm
  simpa [smul_dotProduct, single_one_dotProduct] using this

theorem mem_kerH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (v : Fin (r τ) → Ω) :
    v ∈ D.kerH R p τ χ ↔ ∃ b, (v, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.kerH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_imH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (c : Fin (s τ) → Ω) :
    c ∈ D.imH R p τ χ ↔ ∃ b, (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.imH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

def gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω)) :=
  D.Gam τ ⊓ (⊤ : AddSubgroup (Fin (r τ) → Ω)).prod (D.hh R p χ)

def delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω)) :=
  D.Del τ ⊓ (D.hh R p χ).prod (⊤ : AddSubgroup (Fin (s τ) → Ω))

theorem mem_gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (a : Fin (r τ) → Ω) (b : Fin n → Ω) :
    (a, b) ∈ gamH D R p τ χ ↔ (a, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [gamH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (b : Fin n → Ω) (c : Fin (s τ) → Ω) :
    (b, c) ∈ delH D R p τ χ ↔ (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [delH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

end Lattices

section Families

variable (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem isLatFamily_inf_prod_right (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V₁} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (⊤ : AddSubgroup V).prod (H c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨trivial, hH.1 c hc a ha _ h2⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨trivial, ?_⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

theorem isLatFamily_inf_prod_left (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (H c).prod (⊤ : AddSubgroup V₁) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨hH.1 c hc a ha _ h2, trivial⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

end Families

theorem relSeq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD hG hF τ
  have hhfam := (((GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hD).2 τ).2.2.2.2 hG).1
  obtain ⟨-, -, -, -, hGam, hDel, -⟩ := hD.fam τ
  have h0 : χ τ 0 = 0 := (hD.char.2.2.2.2 τ).1
  have h1 : χ τ 1 = 1 := (hD.char.2.2.2.2 τ).2
  have h0' : algebraMap O Ω (χ τ 0) = 0 := by rw [h0, map_zero]
  have h1' : algebraMap O Ω (χ τ 1) = 1 := by rw [h1, map_one]
  have hstd : ∀ c, mseg x c ≠ 0 → stdLat (chartRing O (mseg x) c) (Fin n) ≤
      (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) :=
    fun c hc => std_le_hh (D c) _ p _ (hD.base c hc) _ h0' h1'
  refine ⟨fun c => gamH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    fun c => delH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    ⟨isLatFamily_inf_prod_right O x hGam hhfam, fun c hc => ?_⟩,
    ⟨isLatFamily_inf_prod_left O x hDel hhfam, fun c hc => ?_⟩, fun c hc => ?_⟩
  · have hB := hD.base c hc
    have hk := (hF c hc).ker τ
    refine ⟨fun v b hvb => ?_, fun v hv => ?_, fun b => ?_, fun v hv => ?_⟩
    · have h := (mem_gamH _ _ _ _ _ _ _).1 hvb
      refine ⟨?_, h.2⟩
      beta_reduce
      rw [← hk]
      exact (mem_kerH _ _ _ _ _ _).2 ⟨b, h⟩
    · beta_reduce at hv
      rw [← hk] at hv
      obtain ⟨b, h⟩ := (mem_kerH _ _ _ _ _ _).1 hv
      exact ⟨b, (mem_gamH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_gamH]
      exact ⟨fun h => ((hB.gam τ).2.1 b).1 h.1, fun h => ⟨((hB.gam τ).2.1 b).2 h, hstd c hc h⟩⟩
    · exact (mem_gamH _ _ _ _ _ _ _).2 ⟨((hB.gam τ).2.2 v).2 hv, zero_mem _⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun b e hbe => ?_, fun b hb => ?_, fun e => ?_, fun b hb => ?_⟩
    · have h := (mem_delH _ _ _ _ _ _ _).1 hbe
      refine ⟨h.2, ?_⟩
      beta_reduce
      rw [← hi]
      exact (mem_imH _ _ _ _ _ _).2 ⟨b, h⟩
    · obtain ⟨e, he⟩ := ((hB.del τ).1 b).2
        (smul_mem_std_of_mem_hh (D c) _ p _ _ ((hF c hc).le_af τ) hb)
      exact ⟨e, (mem_delH _ _ _ _ _ _ _).2 ⟨he, hb⟩⟩
    · rw [mem_delH]
      exact ⟨fun h => ((hB.del τ).2.2.1 e).1 h.1, fun h => ⟨((hB.del τ).2.2.1 e).2 h, zero_mem _⟩⟩
    · refine (mem_delH _ _ _ _ _ _ _).2 ⟨((hB.del τ).2.2.2 b).2 ⟨0, ((hB.gam τ).2.1 b).2 hb⟩, hstd c hc hb⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun v hv => ?_, fun e he => ?_, fun b => ?_⟩
    · exact ((hB.gam τ).2.2 v).1 ((mem_gamH _ _ _ _ _ _ _).1 hv).1
    · beta_reduce at he
      rw [← hi] at he
      obtain ⟨b, h⟩ := (mem_imH _ _ _ _ _ _).1 he
      exact ⟨b, (mem_delH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_delH]
      constructor
      · rintro ⟨h, hb⟩
        obtain ⟨a, ha⟩ := ((hB.del τ).2.2.2 b).1 h
        exact ⟨a, (mem_gamH _ _ _ _ _ _ _).2 ⟨ha, hb⟩⟩
      · rintro ⟨a, ha⟩
        have h := (mem_gamH _ _ _ _ _ _ _).1 ha
        exact ⟨((hB.del τ).2.2.2 b).2 ⟨a, h.1⟩, h.2⟩

end GlobalTheory.CompanionTheory.Ar.Num.RelSeq
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBoundStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.injective_mod_p_lattice_character_bound : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | exact GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RelSeq.relSeq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplit

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.GoodModel

theorem algebraMap_injective_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have h3 := h.2.2.1
  have hmem : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap]
    simp only [mcIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap]
    erw [MvPolynomial.aeval_C]
    rw [MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h3] at hmem
  simpa using hmem

theorem quotExact_congr {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {V V₁ V₂ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
    [AddCommGroup V₂] [Module Ω V₂]
    {A A' A₂ A₂' : (∀ k, ι k) → AddSubgroup V} {B B' B₂ B₂' : (∀ k, ι k) → AddSubgroup V₁}
    {C C' C₂ C₂' : (∀ k, ι k) → AddSubgroup V₂}
    (hA : ∀ s, mseg x s ≠ 0 → A s = A₂ s) (hA' : ∀ s, mseg x s ≠ 0 → A' s = A₂' s)
    (hB : ∀ s, mseg x s ≠ 0 → B s = B₂ s) (hB' : ∀ s, mseg x s ≠ 0 → B' s = B₂' s)
    (hC : ∀ s, mseg x s ≠ 0 → C s = C₂ s) (hC' : ∀ s, mseg x s ≠ 0 → C' s = C₂' s)
    (h : QuotExact O x A A' B B' C C') : QuotExact O x A₂ A₂' B₂ B₂' C₂ C₂' := by
  obtain ⟨Γ, Δ, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  refine ⟨Γ, Δ, ⟨h1, fun s hs => ?_⟩, ⟨h3, fun s hs => ?_⟩, fun s hs => ?_⟩
  · have := h2 s hs
    rw [hA s hs, hA' s hs, hB s hs, hB' s hs] at this
    exact this
  · have := h4 s hs
    rw [hB s hs, hB' s hs, hC s hs, hC' s hs] at this
    exact this
  · have := h5 s hs
    rw [hA' s hs, hC s hs] at this
    exact this

theorem arith_first (a b c rw rp : ℤ) (P k : ℕ) (hP : 2 ≤ P) (e : a + b = c - (k : ℤ) * rw)
    (bd : ((P - 1 : ℕ) : ℤ) * rw = ((1 : ℕ) : ℤ) * rp) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rp : ℝ) / ((P : ℝ) - 1) := by
  have hP1 : (P : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    intro h0
    linarith
  have bdR : ((P : ℝ) - 1) * (rw : ℝ) = (rp : ℝ) := by
    have h1 := congrArg (Int.cast : ℤ → ℝ) bd
    have h2 : (((P - 1 : ℕ) : ℤ) : ℝ) = (P : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega), Nat.cast_one]
    rw [Int.cast_mul, h2, Int.cast_mul] at h1
    simpa using h1
  have eR : (a : ℝ) + (b : ℝ) = (c : ℝ) - (k : ℝ) * (rw : ℝ) := by exact_mod_cast e
  rw [eR, ← bdR]
  field_simp

theorem arith_second {m : ℕ} (A B : Fin m → ℤ) (Λ : ℤ) (P k : ℕ) (hk : 1 ≤ k)
    (e : (k : ℤ) * Λ = (-1) ^ (k - 1) * ∑ i, (A i - (P : ℤ) ^ k * B i)) :
    (P : ℝ) ^ k * ((((-1) ^ k * ∑ i, B i : ℤ)) : ℝ) =
      ((((-1) ^ k * ∑ i, A i : ℤ)) : ℝ) + (k : ℝ) * (Λ : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hz : (P : ℤ) ^ (j + 1) * ((-1) ^ (j + 1) * ∑ i, B i) =
      (-1) ^ (j + 1) * ∑ i, A i + ((j + 1 : ℕ) : ℤ) * Λ := by
    rw [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.add_sub_cancel]
    ring
  exact_mod_cast hz

theorem relations : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hM F _ _ _ n Sg _ r s p hp w χ φ D hD hG1 hG2 hF hX Lie W Om OmHT hB
  have inj : Function.Injective (algebraMap O Ω) := algebraMap_injective_of_model hM
  obtain ⟨hp0, ⟨u, hu, hwu⟩, -, h01, hχ⟩ := hD.char
  have hp2 : 2 ≤ p := hp.two_le
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hwu
    exact hp0 (by simpa [hu.ne_zero] using hwu.symm)
  have hwΩ : algebraMap O Ω w ≠ 0 := (map_ne_zero_iff _ inj).2 hw0
  have hCD : ∀ c, CharData (chartRing O (mseg x) c) p (algebraMap O Ω w)
      (fun τ a => algebraMap O Ω (χ τ a)) := by
    intro c
    refine ⟨?_, Subalgebra.algebraMap_mem _ _, ?_, h01, fun τ => ⟨?_, ?_, fun a => Subalgebra.algebraMap_mem _ _⟩⟩
    · rw [← map_natCast (algebraMap O Ω)]
      exact (map_ne_zero_iff _ inj).2 hp0
    · obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (v * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      rw [← map_natCast (algebraMap O Ω), ← map_mul]
      congr 1
      have : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      calc (p : O) = v * (u * p) := by rw [← mul_assoc, hv, one_mul]
        _ = v * w ^ (p - 1) := by rw [hwu]
        _ = v * w ^ (p - 2) * w := by rw [this, mul_assoc]
    · simp [(hχ τ).1]
    · simp [(hχ τ).2]
  have hfc := GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x inj p hp w χ φ D hD
  have hgb := fun c (hc : mseg x c ≠ 0) =>
    GlobalTheory.T.lattice_good_base_change (D c) (chartRing O (mseg x) c) p _ _ (hCD c) (hD.base c hc) (hG1 c hc)
  have hbf := GlobalTheory.T.lattice_families_glue_to_bundle O Ω K ι x
  have hbo := GlobalTheory.T.chart_bundle_product O Ω K ι x
  have hXb : ∀ τ i, ∃ E : ChartBundle O (mseg x) 1 Ω, ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i := fun τ i =>
    (hbf 1 Ω).1 _ ((hfc.2 τ).2.1 i).1 (fun c hc => ((hgb c hc).1 τ).2.2.2 i)
  choose Xb hXb using hXb
  obtain ⟨T, hT⟩ := hbo.2.2.1 1 0 one_ne_zero
  obtain ⟨Tn, hTn⟩ := hbo.2.2.2.1 n (Fin n → Ω) (Pi.basisFun Ω (Fin n))
  have hTn' : ∀ c, mseg x c ≠ 0 → Tn.lat c = stdLat (chartRing O (mseg x) c) (Fin n) := by
    intro c hc
    ext v
    rw [hTn c hc v]
    simp [stdLat, AddSubgroup.mem_pi]
  have hH : ∀ τ, ∃ E : ChartBundle O (mseg x) n (Fin n → Ω), ∀ c, mseg x c ≠ 0 →
      E.lat c = (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) := fun τ =>
    (hbf n _).1 _ ((hfc.2 τ).2.2.2.2 hG1).1 (fun c hc => ((hgb c hc).1 τ).2.1)
  choose H hH using hH
  have hLa : ∀ τ, ∃ E : ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω),
      IsScaled x (algebraMap O Ω w)⁻¹ (Lie τ).lat E.lat := fun τ =>
    hbo.2.1 _ _ (Lie τ) _ (inv_ne_zero hwΩ)
  choose La hLa using hLa
  have hdiv : ∀ {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω),
      v ∈ divLat (algebraMap O Ω w) L ↔ algebraMap O Ω w • v ∈ L := fun _ _ => Iff.rfl
  have hLa' : ∀ τ c, mseg x c ≠ 0 →
      (La τ).lat c = divLat (algebraMap O Ω w) ((Lie τ).lat c) := by
    intro τ c hc
    ext v
    rw [hLa τ c hc v]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact he
    · intro hv
      exact ⟨algebraMap O Ω w • v, (hdiv _ _).1 hv, (inv_smul_smul₀ hwΩ v).symm⟩
  have hSc : ∀ τ, IsScaled x (algebraMap O Ω w) (La τ).lat (Lie τ).lat := by
    intro τ c hc v
    rw [hLa' τ c hc]
    constructor
    · intro hv
      refine ⟨(algebraMap O Ω w)⁻¹ • v, ?_, (smul_inv_smul₀ hwΩ v).symm⟩
      rw [hdiv, smul_inv_smul₀ hwΩ]
      exact hv
    · rintro ⟨e, he, rfl⟩
      exact (hdiv _ _).1 he
  have hLW : ∀ τ, LatLE O x (Lie τ) (W τ) := by
    intro τ c hc
    rw [(hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).1
  have hWLa : ∀ τ, LatLE O x (W τ) (La τ) := by
    intro τ c hc
    rw [hLa' τ c hc, (hB τ c hc).1, (hB τ c hc).2.1]
    exact ((hD.base c hc).incl τ).2.1
  have hOm : ∀ τ, SameGeneric O x (Om τ) (OmHT τ) := by
    intro τ c hc
    rw [(hB τ c hc).2.2.1, (hB τ c hc).2.2.2]
    have hi := (hD.base c hc).incl τ
    refine ⟨fun v hv => ⟨w, hw0, hi.2.2.2 hv⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    rw [map_one, one_smul]
    exact hi.2.2.1 hv
  have hRH := fun τ => GlobalTheory.T.model_over_mod_p_lattice_character O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
    (fun τ i c hc => hXb τ i c hc) hT τ (H τ) Tn (fun c hc => ⟨hH τ c hc, hTn' c hc⟩)
  have hSeq : ∀ τ, QuotExact O x (La τ).lat (W τ).lat (H τ).lat Tn.lat (Om τ).lat (OmHT τ).lat := by
    intro τ
    refine quotExact_congr ?_ ?_ ?_ ?_ ?_ ?_ (GlobalTheory.T.injective_mod_p_lattice_character_bound O Ω K ι x inj p hp w χ φ D hD hG1 hF τ)
    · intro c hc; rw [hLa' τ c hc, (hB τ c hc).1]
    · intro c hc; rw [(hB τ c hc).2.1]
    · intro c hc; rw [hH τ c hc]
    · intro c hc; rw [hTn' c hc]
    · intro c hc; rw [(hB τ c hc).2.2.1]
    · intro c hc; rw [(hB τ c hc).2.2.2]
  intro k hk1 hk2 q L Q hQ
  refine ⟨fun τ => (((-1) ^ k * ∑ i, ck O x d 1 (Xb τ i) T k L Q : ℤ) : ℝ), fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨Ew, hEw⟩ := hbo.2.1 _ _ (Lie τ) _ hwΩ
    have bd := ((GlobalTheory.T.dvr_bundle_statement_d O Ω K ι) x d (r τ) _ (Lie τ) Ew w hw0 hM hEw k hk1 hk2 q L Q hQ).2
      (p - 1) 1 (p : O) u hu (by omega) (by rw [pow_one]; exact hwu)
    have l61 := GlobalTheory.T.hodge_lie_bundle_intersection O Ω K ι x d (r τ) (s τ) n _ _ _ (Lie τ) (W τ) (La τ) (Om τ) (OmHT τ) Tn (H τ)
      w hw0 hM (hLW τ) (hWLa τ) (hSc τ) (hOm τ) (hRH τ).1 (hSeq τ) k hk1 hk2 q L Q hQ
    rw [(hRH τ).2 k hk1 hk2 q L Q hQ] at l61
    exact arith_first _ _ _ _ _ p k hp2 l61 bd
  · exact arith_second _ _ _ p k hk1
      (GlobalTheory.T.model_over_mod_p_lattice_permuted O Ω K ι x d hM p hp w χ φ D hD hG1 hG2 hF hX Xb T
        (fun τ i c hc => hXb τ i c hc) hT Lie W Om OmHT hB τ k hk1 hk2 q L Q hQ)

end GlobalTheory.CompanionTheory.Ar.Num.GoodModel
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplitStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.model_over_mod_p_lattice_eigen_split : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations | exact GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GoodModel.relations <;> assumption)
end
end
