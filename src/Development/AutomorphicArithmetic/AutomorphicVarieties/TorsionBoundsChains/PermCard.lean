module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.GroupHomologyLongExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.OrbStep
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermTrans

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CardStep

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cardStep :
    ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : B →+ C)
      (a c : ℕ), Function.Exact f g → CardLe A a → CardLe C c → CardLe B (a * c) := by
  intro A B C _ _ _ f g a c hex hA hC
  obtain ⟨hAf, ha⟩ := hA
  obtain ⟨hCf, hc⟩ := hC
  have hker : g.ker = f.range := AddMonoidHom.exact_iff.mp hex
  have h1 : Nat.card g.ker ≤ Nat.card A := by
    rw [hker]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h2 : g.ker.index ≤ Nat.card C := by
    rw [AddSubgroup.index_ker]
    exact Finite.card_subtype_le _
  haveI hfin1 : Finite g.ker := by
    rw [hker]
    exact Finite.of_surjective _ f.rangeRestrict_surjective
  have hpos1 : 0 < Nat.card g.ker := Nat.card_pos
  have hpos2 : 0 < g.ker.index := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos
  have hcard := AddSubgroup.card_mul_index g.ker
  refine ⟨Nat.finite_of_card_ne_zero (by rw [← hcard]; positivity), ?_⟩
  rw [← hcard]
  exact Nat.mul_le_mul (h1.trans ha) (h2.trans hc)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermEmpty

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permEmpty :
    ∀ (G X : Type) [Group G] [MulAction G X] [IsEmpty X] (j : ℕ),
      CardLe (groupHomology (permRep G X) j) 1 := by
  intro G X _ _ _ j
  have hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j) := by
    change Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))
    infer_instance
  have hZ : Subsingleton (groupHomology.cycles (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    exact (ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1
      inferInstance (Subsingleton.elim _ _)
  have hH : Subsingleton (groupHomology (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    induction a using groupHomology_induction_on with
    | h a =>
      induction b using groupHomology_induction_on with
      | h b => rw [Subsingleton.elim a b]
  haveI := hH
  exact ⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermSplit

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permSplit :
    ∀ (G X : Type) [Group G] [MulAction G X] (U V : SubMulAction G X), (∀ y, y ∈ V ↔ y ∉ U) →
      ∃ (f : permRep G U ⟶ permRep G X) (g : permRep G X ⟶ permRep G V),
        Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  intro G X _ _ U V hUV
  let F : (perm G U).IntertwiningMap (perm G X) :=
    { toLinearMap := Finsupp.lmapDomain ℤ ℤ (Subtype.val : U → X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        simp only [LinearMap.comp_apply, perm_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        congr 1 }
  let Gm : (perm G X).IntertwiningMap (perm G V) :=
    { toLinearMap := Finsupp.lsubtypeDomain (V : Set X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        ext ⟨y, hy⟩
        change (Finsupp.mapDomain (fun x => g • x) f) y =
          (Finsupp.mapDomain (fun v : V => g • v) (Finsupp.subtypeDomain (· ∈ V) f)) ⟨y, hy⟩
        have hy' : g⁻¹ • y ∈ V := V.smul_mem _ hy
        have e2 : (⟨y, hy⟩ : V) = g • (⟨g⁻¹ • y, hy'⟩ : V) := Subtype.ext (by simp)
        rw [e2, Finsupp.mapDomain_apply_of_injective (MulAction.injective g), Finsupp.subtypeDomain_apply]
        have e1 : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
        conv_lhs => rw [e1]
        rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective g)] }
  refine ⟨Rep.ofHom F, Rep.ofHom Gm, ?_, ?_, ?_⟩
  · rw [Rep.hom_ofHom]
    change Function.Injective (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [Rep.hom_ofHom, Rep.hom_ofHom]
    intro y
    change Finsupp.subtypeDomain (· ∈ V) y = 0 ↔
      y ∈ Set.range (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    constructor
    · intro hy0
      refine ⟨Finsupp.subtypeDomain (· ∈ U) y, ?_⟩
      ext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : X) from rfl, Finsupp.mapDomain_apply_of_injective Subtype.val_injective,
          Finsupp.subtypeDomain_apply]
      · rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨u, rfl⟩; exact hx u.2)]
        have hxV : x ∈ V := (hUV x).2 hx
        have h1 := DFunLike.congr_fun hy0 ⟨x, hxV⟩
        simp only [Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
        exact h1.symm
    · rintro ⟨u, rfl⟩
      ext ⟨x, hx⟩
      rw [Finsupp.subtypeDomain_apply, Finsupp.mapDomain_notin_range _ _ ?_]
      · simp
      · rintro ⟨w, rfl⟩
        exact ((hUV _).1 hx) w.2
  · rw [Rep.hom_ofHom]
    intro h
    refine ⟨Finsupp.mapDomain (Subtype.val : V → X) h, ?_⟩
    ext ⟨y, hy⟩
    change Finsupp.mapDomain (Subtype.val : V → X) h ((⟨y, hy⟩ : V) : X) = h ⟨y, hy⟩
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermCard

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permCard :
    ∀ (G : Type) [Group G] (s j A : ℕ) (X : Type) [MulAction G X], OrbLe G X A → StabLe G X s →
      1 ≤ s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
  intro G _ s j A
  have hempty : ∀ (A : ℕ) (X : Type) [MulAction G X] [IsEmpty X], 1 ≤ s →
      CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (A * s ^ (j + 1))) := by
    intro A X _ _ hs
    obtain ⟨h1, h2⟩ := permEmpty G X (j + 1)
    exact ⟨h1, h2.trans (Nat.one_le_pow _ _ hs)⟩
  induction A with
  | zero =>
    intro X _ hO _ hs
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨hf, hc⟩ := hO
      haveI : Nonempty (MulAction.orbitRel.Quotient G X) := ⟨Quotient.mk'' x⟩
      have := Nat.card_pos (α := MulAction.orbitRel.Quotient G X)
      omega⟩
    exact hempty 0 X hs
  | succ A ih =>
    intro X _ hO hS hs
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact hempty _ X hs
    · obtain ⟨U, V, hUV, hne, htr, hSU, hSV, hOV⟩ := orbStep G X A s x hO hS
      obtain ⟨f, g, hf, hfg, hg⟩ := permSplit G X U V hUV
      obtain ⟨⟨u, v, huv⟩, -⟩ := les G _ _ _ f g hf hfg hg (j + 1)
      have h1 := permTrans G U s j hSU
      have h2 := ih V hOV hSV hs
      have h3 := cardStep _ _ _ u v _ _ huv h1 h2
      have e : s ^ (s ^ (j + 1)) * s ^ (A * s ^ (j + 1)) = s ^ ((A + 1) * s ^ (j + 1)) := by
        rw [← pow_add]; congr 1; ring
      rwa [e] at h3
end
end
