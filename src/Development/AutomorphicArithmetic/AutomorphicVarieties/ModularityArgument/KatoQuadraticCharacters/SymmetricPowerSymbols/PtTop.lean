module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ChB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.EdgeGeo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.FixInv
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRingOfIntegersOfHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.IsSymb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsIntegralOfMemOverY
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.ValComapLtOne

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.IsoEx

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

theorem UpperTheory.V.Z.Kato.Sym.PT.isoEx :
    UpperTheory.V.Z.Kato.Sym.PT.IsoEx := by
  intro Ω _ _ _ ε X M
  let L := topL X M
  let L' : IntermediateField Ω X.K :=
    { L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }
  let F : IntermediateField Ω X.K := IntermediateField.adjoin Ω {X.jK}
  have hFL : F ≤ L' :=
    IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)
  have hle : F.toSubfield ≤ L := fun x hx => hFL hx
  letI : Algebra F L := (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower F L X.K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L X.K :=
    ⟨fun f => (X.alg_j f).tower_top L⟩
  haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)
  let e : topBar X M ≃ₐ[L] Kb X := IsAlgClosure.equiv L (topBar X M) (Kb X)
  refine ⟨e.toRingEquiv, fun f => ?_⟩
  change e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply L X.K (Kb X) f
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPt

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.PT.ptGal :
    UpperTheory.V.Z.Kato.Sym.PT.PtGal := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF e he η hη s hs w hw f hf
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hm : 0 < l ^ n := pow_pos hl.pos n
  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  obtain ⟨-, -, -, -, -, -, hlift, -⟩ := admB Ω ε X
  obtain ⟨σ, hσ⟩ := hlift (X.gal s)
  obtain ⟨c1, c2, c3, c4, c5⟩ := cjB Ω ε X M e he
  obtain ⟨-, -, -, -, -, -, hcyc⟩ := lgB Ω ε X (l ^ n) hm
  have hfix : FixF X M σ := fun g hg => by
    rw [hσ g, ((mem_mdl_iff X _ _ _).1 hg).2 s hs]
  have hc : cyc (l ^ n) s = 1 := by
    have hζ := isPrimitiveRoot_eOm ε hm.ne'
    have h1 := (hcyc s s).2.2 _ hζ.pow_eq_one
    rw [(mem_fixMu_iff s).1 hs _ ((hζ.pow_eq_one_iff_dvd M).2 hd)] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt (cyc (l ^ n) s)) (ZMod.val_lt (1 : ZMod (l ^ n))) (by
      rw [← h1, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ.pow_eq_one, pow_one])
    exact ZMod.val_injective _ h2
  have hL : IsTopLift X M s (cj X M e σ) := fun g =>
    ⟨⟨X.gal s g, gal_mem_topL X hM.ne' hs g.2⟩, rfl, e.injective (by rw [c1 σ hfix, he, he, hσ])⟩
  have h0 := isTopLift_topLift X hM.ne' hs
  have hg := IsTopLift.inv_mul_mem_geo h0 hL
  obtain ⟨hw0, θ, hθ, hk⟩ := hw
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hθ
    exact hw0 ((algebraMap (topL X M) (topBar X M)).injective (by rw [← hθ, map_zero]))
  refine ⟨σ, hσ, e θ, by rw [← map_pow, hθ, he, hf], fun h hh => ?_⟩
  obtain ⟨hhF, hgeo⟩ := c3 h fun g _ => hh g
  have k1 : ka X (l ^ n) (e θ) h = GlobalTheory.NeedB.kum (K := topF X M) (N := l ^ n) (topZeta X M l n) θ (cj X M e h) := by
    unfold ka
    rw [← c1 h hhF]
    exact c5 l n hl.ne_zero h hhF _ _ hθ0 _
      (TopW.apply_eq_kum (isPrimitiveRoot_topZeta X M hl.ne_zero n) hw0 hθ hgeo)
  have hconj : (topLift X M s)⁻¹ * cj X M e h * (topLift X M s)⁻¹⁻¹ ∈ geo (topF X M) (topL X M) (topBar X M) := by
    rw [TopW.mem_geo] at hgeo ⊢
    intro z
    obtain ⟨z', -, hz⟩ := h0 z
    rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hz, hgeo, ← hz, ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]
  have k2 : GlobalTheory.KEdge.edge (topChar X M l n u) (topChar X M l n v) η (cj X M e σ)⁻¹ (cj X M e h) =
      GlobalTheory.KEdge.edge (topChar X M l n u) (topChar X M l n v) η (topLift X M s)⁻¹ (cj X M e h) := by
    have e1 : (cj X M e σ)⁻¹ = ((topLift X M s)⁻¹ * cj X M e σ)⁻¹ * (topLift X M s)⁻¹ := by group
    rw [e1, TopW.edge_mul_conj, (edgeGeo _ _ _ _ _ η hη.1).1 _ (inv_mem hg) _ hconj, zero_add]
  have hi := (c2 σ σ hfix hfix).2
  have e2 : cj X M e (σ⁻¹ * h * σ) = (cj X M e σ)⁻¹ * cj X M e h * cj X M e σ := by
    rw [(c2 _ σ (c2 _ h hi.1 hhF).1 hfix).2.2.1, (c2 _ h hi.1 hhF).2.2.1, hi.2.2]
  have a := (chB Ω ε X l n M hl hM hd u hu.1 huF e he).2
  have b := (chB Ω ε X l n M hl hM hd v hv.1 hvF e he).2
  rw [k1, hk _ hgeo, ← k2, TopW.edge_inv, hc, ← e2, ← a h hhF, ← a σ hfix, ← b h hhF, ← b σ hfix]
  simp only [dif, Pt.mv, topPt, one_pow, one_mul]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopPtAlt

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.PT.ptGam :
    UpperTheory.V.Z.Kato.Sym.PT.PtGam := by
  intro Ω _ _ _ ε X l n M hl hM hdiv u v hu hv huF hvF e he η hη γ hγ
  obtain ⟨-, hmul, hgeo, -, -⟩ := cjB Ω ε X M e he
  obtain ⟨σ, hσ⟩ := (admB Ω ε X).2.2.2.2.2.2.1 (slR X (ofSL γ))
  have hσL : ∀ f ∈ topL X M, σ (io X f) = io X f := by
    intro f hf
    rw [hσ f]
    congr 1
    exact (mem_lev_iff X _ f).1 hf γ hγ
  obtain ⟨hσF, hσg⟩ := hgeo σ hσL
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨-, -, hlg, -, -, -, hcyc⟩ := lgB Ω ε X (l ^ n) hm
  refine ⟨σ, hσ, 1, by simp, ?_⟩
  intro h hh
  have hhF : FixF X M h := fun f _ => hh f
  obtain ⟨-, hhg⟩ := hgeo h (fun f _ => hh f)
  obtain ⟨-, hσiF, -, hσinv⟩ := hmul σ σ hσF hσF
  obtain ⟨h1F, -, h1eq, -⟩ := hmul σ⁻¹ h hσiF hhF
  obtain ⟨-, -, h2eq, -⟩ := hmul (σ⁻¹ * h) σ h1F hσF
  have hU := chB Ω ε X l n M hl hM hdiv u hu.1 huF e he
  have hV := chB Ω ε X l n M hl hM hdiv v hv.1 hvF e he
  have e0 : ka X (l ^ n) 1 h = 0 := by
    simp only [ka, map_one]
    exact hlg 1 1 0 one_ne_zero (by simp)
  have hE := (edgeGeo (topGal X M) (l ^ n) (geo (topF X M) (topL X M) (topBar X M))
    (topChar X M l n u) (topChar X M l n v) η hη.1).1 (cj X M e σ)⁻¹ (inv_mem hσg) (cj X M e h) hhg
  rw [TopW.edge_inv] at hE
  rw [e0]
  simp only [dif, Pt.mv, topPt, (hcyc 1 1).2.1, one_pow, one_mul]
  have k1 : lg X (l ^ n) (σ (e (topRoot X M (l ^ n) u))) (e (topRoot X M (l ^ n) u))
      = ka X (l ^ n) (e (topRoot X M (l ^ n) u)) σ := rfl
  have k2 : lg X (l ^ n) (σ (e (topRoot X M (l ^ n) v))) (e (topRoot X M (l ^ n) v))
      = ka X (l ^ n) (e (topRoot X M (l ^ n) v)) σ := rfl
  rw [k1, k2, hU.2 h hhF, hU.2 σ hσF, hV.2 h hhF, hV.2 σ hσF, h2eq, h1eq, hσinv]
  linear_combination (-1 : ZMod (l ^ n)) * hE
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.TopUnit

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT Polynomial

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_int (X : Tower Ω ε) (M : ℕ) (f : topL X M) (h : IsIntegral (Algebra.adjoin Ω {X.jK}) (f : X.K)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  obtain ⟨p, hpm, hp⟩ := h
  have hmem : ∀ P : Polynomial Ω, aeval X.jK P ∈ Algebra.adjoin Ω {X.jK} := fun P => by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨P, rfl⟩
  let g : Polynomial Ω →+* Algebra.adjoin Ω {X.jK} :=
    ((aeval X.jK).codRestrict (Algebra.adjoin Ω {X.jK}) hmem).toRingHom
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ :=
    lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts p).mpr fun n => hg _) hpm
  refine ⟨q, hqm, Subtype.val_injective ?_⟩
  have e1 : ((topL X M).subtype).comp (algebraMap (Polynomial Ω) (topL X M)) =
      (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := RingHom.ext fun P => coe_jPoly X _ P
  have e2 : (algebraMap (Algebra.adjoin Ω {X.jK}) X.K).comp g =
      (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := RingHom.ext fun P => rfl
  have key := Polynomial.hom_eval₂ q (algebraMap (Polynomial Ω) (topL X M)) (topL X M).subtype f
  rw [e1] at key
  rw [← hq, eval₂_map, e2] at hp
  show (topL X M).subtype (eval₂ (algebraMap (Polynomial Ω) (topL X M)) f q) = ((0 : topL X M) : X.K)
  rw [key, ZeroMemClass.coe_zero]
  exact hp

theorem isTopUnit [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (M : ℕ) {u : X.K} (hu : IsU X u) (hF : u ∈ topF X M) :
    TopUnits.IsTopUnit X M u :=
  ⟨hu.1, hF, mdl_le_lev X _ _ hF, mem_int X M _ (intU Ω ε X M u hu).1, mem_int X M _ (intU Ω ε X M u hu).2⟩

end UpperTheory.V.Z.Kato.Sym.PT
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtTop

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

attribute [local instance] algMdl

theorem UpperTheory.V.Z.Kato.Sym.ptTop :
    UpperTheory.V.Z.Kato.Sym.PtTop := by
  intro Ω _ _ _ ε X l n M hl hM hd u v hu hv huF hvF
  obtain ⟨e, he⟩ := isoEx Ω ε X M
  obtain ⟨h1, h2⟩ := TopEta.spec_of_units X hM.ne' hl.ne_zero hd (isTopUnit X M hu huF) (isTopUnit X M hv hvF)
  have hη := isTopEta_topEta X M h1
  refine ⟨_, ptIs Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη, ptGam Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη,
    fun s hs => ?_⟩
  have hw := h2 (topLift X M s)⁻¹
  have h0 : wGen X M l n u v s ≠ 0 := fun h => hw.1 (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, rfl, ptGal Ω ε X l n M hl hM hd u v hu hv huF hvF e he _ hη s hs _ hw _ rfl⟩
end
end
