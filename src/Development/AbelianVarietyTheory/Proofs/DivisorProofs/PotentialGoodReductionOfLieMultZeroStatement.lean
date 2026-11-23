module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveAnnihilatorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPartFibreLieAlgebraCharactersStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqZeroOfDualKilledByTensor

section

@[expose] public section

open NumberField Polynomial

namespace GlobalTheory

theorem ringOfIntegers_action_injective (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Nontrivial X] (ρ : 𝓞 F →+* Module.End ℤ X) :
    Function.Injective ρ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ RingHom.ker ρ := ha
  have hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ := Ideal.absNorm_mem _
  rw [RingHom.mem_ker, map_natCast] at hn
  obtain ⟨χ, hχ⟩ := exists_ne (0 : X)
  have h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0 := by
    have := congrArg (fun f : Module.End ℤ X => f χ) hn
    simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℤ] at h1
  have h2 : Ideal.absNorm (RingHom.ker ρ) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hχ
  rw [Ideal.absNorm_eq_zero_iff] at h2
  rw [h2] at hmem
  simpa using hmem

theorem dvd_coord_of_action_dvd (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Nontrivial X]
    (ρ : 𝓞 F →+* Module.End ℤ X) (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F))
    (p : ℤ) (hp : p ≠ 0) (a : 𝓞 F)
    (h : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      p ∣ (Module.Free.chooseBasis ℤ X).repr (ρ a χ) r) :
    ∀ i, p ∣ b.repr a i := by
  set B := Module.Free.chooseBasis ℤ X
  let T : Module.End ℤ X := B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)
  have hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a := by
    apply B.ext
    intro s
    rw [Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]
    conv_rhs => rw [← B.sum_repr (ρ a (B s))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.mul_ediv_cancel' (h _ r)]
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) T
  have hf' : aeval T f = 0 := by rw [aeval_def]; exact hf
  have h1 := Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'
  rw [hT] at h1
  have h2 : aeval a (f.scaleRoots p) = 0 := by
    apply ringOfIntegers_action_injective F X ρ
    rw [map_zero]
    have := Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)
    change ρ.toIntAlgHom _ = 0
    rw [← this]
    exact h1
  have h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, h2, map_zero]
  have hpF : (algebraMap ℤ F p) ≠ 0 := by simpa using hp
  set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef
  have hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a := by
    rw [hβdef]; field_simp
  have h4 : eval₂ (algebraMap ℤ F) β f = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p
    rw [hβa, ← aeval_def, h3] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)
  have hβ : IsIntegral ℤ β := ⟨f, hfm, h4⟩
  let y : 𝓞 F := ⟨β, hβ⟩
  have hy : p • y = a := by
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, zsmul_eq_mul]
    have : algebraMap (𝓞 F) F y = β := rfl
    rw [this, ← hβa]
    simp
  intro i
  refine ⟨b.repr y i, ?_⟩
  rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem finrank_eq_zero_of_dual_killed : ∀ (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X)
    (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k),
    w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) →
    Module.finrank ℤ X = 0 := by
  intro F _ _ X _ _ _ ρ k _ ι _ b w hw hyp
  classical
  by_contra hX
  haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)
  set B := Module.Free.chooseBasis ℤ X
  have key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0 := by
    intro χ r
    have := hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_comm]
  have lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r := by
    intro e χ r

    simp [map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · set p := ringChar k with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP k p := ringChar.charP k
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)
    set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef
    have hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r := by
      intro χ r
      rw [lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := congrArg π (key χ r)

      rw [map_sum, map_zero] at this
      rw [← this]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hedef]
      simp [ZMod.natCast_zmod_val, mul_comm]
    have h := GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0
    rw [Module.Basis.repr_sum_self] at h
    apply hπ
    rw [← ZMod.natCast_zmod_val (π (w i0))]
    have h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact_mod_cast h'
  · haveI : CharZero k := by
      have := ringChar.charP k; rw [hp] at this; exact CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)
    set c : ι → ℚ := fun i => π (w i) with hcdef
    set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef
    have he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]
      push_cast; rfl
    have hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        B.repr (ρ (∑ i, e i • b i) χ) r = 0 := by
      intro χ r
      rw [lin]
      have := congrArg π (key χ r)

      rw [map_sum, map_zero] at this
      simp only [map_zsmul] at this
      have h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ)
          = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [he, zsmul_eq_mul, hcdef]; ring
      rw [this, mul_zero] at h2
      exact_mod_cast h2
    have hρ : ρ (∑ i, e i • b i) = 0 := by
      ext χ
      simp only [LinearMap.zero_apply]
      exact B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]
    have ha : (∑ i, e i • b i) = 0 :=
      GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])
    have h0 := congrArg (fun x => b.repr x i0) ha
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0
    have hc0 : c i0 ≠ 0 := hπ
    have : (e i0 : ℚ) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)
    exact this (by exact_mod_cast h0)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqZeroOfDualKilledByTensorStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor : ∀ (F : Type) [Field F] [NumberField F] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X) (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k), w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) → Module.finrank ℤ X = 0 := by
  first | exact @GlobalTheory.finrank_eq_zero_of_dual_killed | exact GlobalTheory.finrank_eq_zero_of_dual_killed | (intros; apply GlobalTheory.finrank_eq_zero_of_dual_killed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZero

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped Matrix

namespace GlobalTheory.PotGoodLie

theorem proper_pull {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (hM : GlobalTheory.SS.IsModel (L := L) A G)
    (hA : IsAbelianScheme A) : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
  obtain ⟨e, -⟩ := hM
  have := hA.proper
  have h : ((Over.pullback (spMap (algebraMap W L))).obj G).hom = e.hom.left ≫ ((Over.pullback (spMap (algebraMap K L))).obj A).hom := (Over.w e.hom).symm
  rw [h]
  have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
    show IsProper (pullback.snd A.hom _)
    infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eq_one_of_lieMult_zero {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G)
    {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (h : LieMult a t τ 0) (w : epsPt t ⟶ G)
    (hw : IsLieEigen a t τ w) : w = 1 := by
  obtain ⟨v, -, H⟩ := h
  obtain ⟨c, ⟨u, -, hu⟩, -⟩ := H w hw
  simpa using hu

theorem lift_ext (V K W L Ω : Type) [CommRing V] [Field K] [CommRing W] [IsDomain W] [Field L] [Field Ω]
    [IsAlgClosed Ω] [Algebra V K] [Algebra V W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    (hc : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hfin : Module.Finite V W) (g : K →+* Ω) : ∃ g' : L →+* Ω, g'.comp (algebraMap K L) = g := by
  letI := g.toAlgebra
  have hint : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have halg : ∀ w : W, IsAlgebraic K (algebraMap W L w) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := hint.isIntegral w
    refine ⟨p.map (algebraMap V K), (hp.map _).ne_zero, ?_⟩
    have := congrArg (algebraMap W L) hpw
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← this, hc]
  haveI : Algebra.IsAlgebraic K L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    rw [div_eq_mul_inv]
    exact IsAlgebraic.mul (halg a) (IsAlgebraic.inv (halg b))
  exact ⟨(IsAlgClosed.lift : L →ₐ[K] Ω).toRingHom, by ext x; simp [RingHom.algebraMap_toAlgebra]⟩

theorem prod_of_add {A B J : Type} [AddCommMonoid A] [CommMonoid B] (φ : A → B) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) (s : Finset J) (g : J → A) : φ (∑ i ∈ s, g i) = ∏ i ∈ s, φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]

theorem exists_ringHom {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) {n : ℕ} (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R) {k : Type} [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X : Over S} (T : (Fin n → k) → (X ⟶ G)) (Tinj : Function.Injective T)
    (Tadd : ∀ c c', T (c + c') = T c * T c')
    (Tact : ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c)) :
    ∃ Mr : O →+* Matrix (Fin n) (Fin n) R, ∀ x, Mr x = M (a.act x) := by
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, (∀ c, T ((P.map f) *ᵥ c) = T ((Q.map f) *ᵥ c)) → P = Q := by
    intro P Q h
    apply Matrix.map_injective hf
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using Tinj (h c)
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have act0 : a.act 0 = 1 := by simpa using a.add 0 0
  refine ⟨{ toFun := fun x => M (a.act x), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun _ => rfl⟩
  · apply key; intro c
    rw [← Tact _ (a.hom 1), a.one]
    simp
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x * y)), mul_comm x y, a.mul, ← Category.assoc, Tact _ (a.hom y), Tact _ (a.hom x),
      Matrix.mulVec_mulVec, ← Matrix.map_mul]
  · apply key; intro c
    rw [← Tact _ (a.hom 0), act0, comp_one]
    simp [T0]
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x + y)), a.add, comp_mul, Tact _ (a.hom x), Tact _ (a.hom y), ← Tadd, Matrix.map_add _ (map_add f),
      Matrix.add_mulVec]

theorem finrank_zero (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (F : Type) [Field F] [NumberField F] (a : OAct (𝓞 F) G) (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] (f : W →+* Ω) (hf : Function.Injective f) (σ : 𝓞 F →+* Ω) (h0 : LieMult a (spMap f) σ 0)
    (E : TorusExtension (GlobalTheory.SS.spFibre G)) : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 := by
  classical
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI : IsCommMonObj G := hG.comm
  obtain ⟨n, M, -, hT⟩ := GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring W G hG.smooth
  obtain ⟨T, Tinj, Trange, Tadd, Tsc, Tact⟩ := hT Ω f
  obtain ⟨Mr, hMr⟩ := exists_ringHom a M f hf T Tinj Tadd Tact
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have hno : ∀ c : Fin n → Ω, (∀ x, ((Mr x).map f).mulVec c = σ x • c) → c = 0 := by
    intro c hc
    have hE : IsLieEigen a (spMap f) σ (T c) := by
      refine ⟨(Trange (T c)).2 ⟨c, rfl⟩, fun x => ?_⟩
      rw [Tact _ (a.hom x), ← hMr, hc, Tsc]
    exact Tinj ((eq_one_of_lieMult_zero a _ σ h0 _ hE).trans T0.symm)
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  obtain ⟨w, ⟨i0, hu⟩, hsum⟩ := GlobalTheory.T.exists_primitive_annihilator' F W Ω f hf n Mr σ hno _ b
  obtain ⟨ρ, U, Uinj, Ufst, Uadd, Usc, Uact⟩ := GlobalTheory.T.toric_part_fibre_lie_algebra_characters (Sp W) G (𝓞 F) a.act a.hom a.one a.mul a.add
    (ResidueField W) (spMap (residue W)) E
  obtain ⟨T', -, T'range, T'add, T'sc, T'act⟩ := hT (ResidueField W) (residue W)
  have T'0 : T' 0 = 1 := by simpa using T'add 0 0
  have U0 : U 0 = 1 := by simpa using Uadd 0 0
  refine GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor F E.X ρ (ResidueField W) _ b (fun i => residue W (w i)) ?_ ?_
  · intro h
    exact (residue_ne_zero_iff_isUnit _).2 hu (congrFun h i0)
  · intro l χ
    obtain ⟨c, hc⟩ := (T'range (U l)).1 (Ufst l)
    have step : ∀ i, U ((AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) =
        T' (residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c)) := by
      intro i
      have e : U (l.comp (ρ (b i)).toAddMonoidHom) = T' ((Mr (b i)).map (residue W) *ᵥ c) := by
        rw [← Uact, ← hc, T'act _ (a.hom _), hMr]
      apply Over.OverMorphism.ext
      rw [Usc, T'sc, e]
    have hv : ∑ i, residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c) = 0 := by
      have := congrArg (fun P => ((residue W).mapMatrix P) *ᵥ c) hsum
      have hsm : ∀ i, (w i • Mr (b i)).map (residue W) = residue W (w i) • (Mr (b i)).map (residue W) := by
        intro i; ext; simp

      simpa [map_sum, Matrix.sum_mulVec, hsm, Matrix.smul_mulVec] using this
    have hL : (∑ i, (AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) = 0 := by
      apply Uinj
      rw [prod_of_add U U0 Uadd, U0, Finset.prod_congr rfl (fun i _ => step i), ← prod_of_add T' T'0 T'add, hv, T'0]
    have := congrArg (fun m => m χ) hL
    simpa using this

theorem potGood_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA F _ _ act Ω _ _ g σ hL
  obtain ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, hsemi, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, ?_⟩
  have hAL := isGrpPullback_pullback A (spMap (algebraMap K L))
  obtain ⟨actL, ⟨h1, h2, h3, h4⟩, hLc⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (algebraMap K L)) A
    ((Over.pullback (spMap (algebraMap K L))).obj A) _ hAL (𝓞 F) act.act act.hom act.one act.mul act.add
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hM _ _ hAL
  obtain ⟨actG, ⟨g1, g2, g3, g4⟩, hGc⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G _ φ hsemi hφ (𝓞 F) actL h1 h2 h3 h4
  let aL : OAct (𝓞 F) ((Over.pullback (spMap (algebraMap K L))).obj A) := ⟨actL, h1, h2, h3, h4⟩
  let aG : OAct (𝓞 F) G := ⟨actG, g1, g2, g3, g4⟩
  obtain ⟨g', hg'⟩ := lift_ext V K W L Ω hc hfin g
  have e1 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ A _ _ (pullback.fst _ _) act aL hAL hLc Ω (spMap g') σ 0
  have hx : spMap g' ≫ spMap (algebraMap K L) = spMap g := by rw [← hg', spMap_comp]
  have e2 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ G _ _ φ aG aL hφ hGc Ω (spMap g') σ 0
  have hG0 : LieMult aG (spMap (g'.comp (algebraMap W L))) σ 0 := by
    rw [spMap_comp]
    exact e2.1 (e1.2 (hx ▸ hL))
  haveI : CharZero Ω := charZero_of_injective_ringHom g.injective
  have hinj : Function.Injective (g'.comp (algebraMap W L)) :=
    g'.injective.comp (IsFractionRing.injective W L)
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsemi (proper_pull A G hM hA) E
    (finrank_zero W G hsemi F aG Ω _ hinj σ hG0 E)

end GlobalTheory.PotGoodLie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZeroStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.potentialGoodReduction_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | exact GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | (intros; apply GlobalTheory.PotGoodLie.potGood_of_lieMult_zero <;> assumption)
end
end
