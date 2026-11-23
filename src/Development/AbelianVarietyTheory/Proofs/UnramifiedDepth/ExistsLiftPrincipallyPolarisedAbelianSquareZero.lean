module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPrincipalLift
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsZpRingHomIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilySRep

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelLargeLevel

theorem isAlgebraic_of_mem_ZP {p M : ℕ} (hM : M ≠ 0) {x : ℂ} (hx : x ∈ ZP p M) : IsAlgebraic ℤ x := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  exact hle hx

theorem exists_siegelFamily_sRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → n ≠ p → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  have halg : Algebra.IsAlgebraic ℤ o := ⟨fun x => by
    have hx : IsAlgebraic ℤ (em.toIntAlgHom x) := by
      change IsAlgebraic ℤ (em x)
      rw [← hi]
      exact isAlgebraic_of_mem_ZP (by omega) (i x).2
    exact (isAlgebraic_algHom_iff em.toIntAlgHom hem.2.2).1 hx⟩
  exact GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst halg F

end GlobalTheory.ZM.SiegelLargeLevel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianLift

private theorem exists_odd_prime_ne (p : ℕ) : ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p := by
  by_cases h : p = 3
  · exact ⟨5, by norm_num, by decide, by omega⟩
  · exact ⟨3, by norm_num, by decide, fun e => h e.symm⟩

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h1 R' _ π hπ hker
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have : IsLocalRing O := by
    have : ValuationRing O := ValuationRing.of_integers v hv
    infer_instance
  obtain ⟨n, hn, hodd, hnp⟩ := exists_odd_prime_ne p
  obtain ⟨j, hj⟩ := GlobalTheory.ZM.SiegelLargeLevel.exists_siegelFamily_sRep GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1
    GlobalTheory.AbLaw.CubeAssembly.cube_gen GlobalTheory.thetaUnifAV_all P.g n h1 hn hodd
  obtain ⟨Ag, hAg⟩ := hj j le_rfl p hp hnp
  have hM0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hcop : ((n ^ j) ^ 2).Coprime p :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hn hp).2 hnp))
  generalize (n ^ j) ^ 2 = M at Ag hAg hM0 hcop
  obtain ⟨β, hβ, hMu, hprim⟩ := GlobalTheory.exists_zp_ringHom_integers p C v O hv M hM0 hcop
  have hζ : β (Geo.Tor.zetaZP p M) ^ M = 1 := hinj (by
    rw [map_pow, map_one]; exact (hprim C (algebraMap O C)).pow_eq_one)
  let ze : Oˣ := (IsUnit.of_pow_eq_one hζ hM0).unit
  have hze : (ze : O) = β (Geo.Tor.zetaZP p M) := rfl
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := GlobalTheory.exists_level_over_integers p C v O hv T P₀ io P φ hφ hL hg P.g M ze rfl hMu
    (hprim C (algebraMap O C))
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre O T P₀ io P φ hφ hL hg _ β P.g M (Geo.Tor.zetaZP p M) ze lev rfl hMu hze
    hprim hl₁ hl₂ hl₃
  obtain ⟨β', c', hc', φ₁, φ₂, hpb, hsq, hiso, -⟩ :=
    GlobalTheory.SiegelLift.exists_principal_lift P.g p M Ag hAg hcop hM0 O R' π hπ hker β hβ c hc
  let k : P.A ⊗ P.A ⟶ c.A ⊗ c.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  have hk : k.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [k]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨c'.A, c'.grp, c'.comm, c'.P, e.inv.left ≫ φ₁, k.left ≫ φ₂, c'.ab, c'.isLB, c'.rig₁, c'.rig₂, c'.symm,
    hc'.1, hc'.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact ((Geo.Tor.isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : Geo.Tor.LBIso (abelian₂ P.A P.L) (c.P.pull k.left) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullSec _ _ k.left hk) (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        hcP.symm
    have hB : Geo.Tor.LBIso (c.P.pull k.left) (c'.P.pull (k.left ≫ φ₂)) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        (Geo.Tor.chartPullSame c'.P _ (fun _ => φ₂) _ k.left fun _ => rfl) hiso
    exact Geo.Tor.LBIso.trans (DVR.linComb_isLB _ P.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _)
      (DVR.linComb_isLB _ c'.isLB _ _) hA hB

end GlobalTheory.AbelianLift
end
end
