module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Module.ZLattice.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PermDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.UnitLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Units.Basic

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.LatDet

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.latDet :
    ∀ (E V : Type) [AddCommGroup E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (lam : E →ₗ[ℤ] V) (δ : Module.End ℤ E) (δV : V →ₗ[ℝ] V), (∀ x, lam (δ x) = δV (lam x)) → LinearMap.ker lam = Submodule.torsion ℤ E → DiscreteTopology (LinearMap.range lam) → Submodule.span ℝ (LinearMap.range lam : Set V) = ⊤ → LinearMap.det δV ≠ 0 → Finite (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ∧ (Nat.card (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) : ℝ) = |LinearMap.det δV| := by
  intro E V _ _ _ _ lam δ δV hcomm hker hdisc hspan hdet
  classical
  set L := LinearMap.range lam with hL
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  have hmaps : ∀ x ∈ L, (δV.restrictScalars ℤ) x ∈ L := by
    rintro _ ⟨y, rfl⟩
    exact ⟨δ y, by simp [hcomm]⟩
  set f : L →ₗ[ℤ] L := (δV.restrictScalars ℤ).restrict hmaps with hf
  have hfv : ∀ y : L, ((f y : L) : V) = δV y := fun y => rfl
  have hVinj : Function.Injective δV := fun a b h =>
    (LinearMap.equivOfDetNeZero δV hdet).injective h
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply hVinj
    rw [← hfv, ← hfv, h]
  have hcard : Nat.card (L ⧸ LinearMap.range f) = (LinearMap.det f).natAbs := by
    rw [← Submodule.natAbs_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hfinj)]
    congr 2
  have hdetf : ((LinearMap.det f : ℤ) : ℝ) = LinearMap.det δV := by
    let b := Module.Free.chooseBasis ℤ L
    let bV := b.ofZLatticeBasis ℝ L
    have hM : (Int.castRingHom ℝ).mapMatrix (LinearMap.toMatrix b b f) =
        LinearMap.toMatrix bV bV δV := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, eq_intCast]
      rw [show bV j = ((b j : L) : V) from b.ofZLatticeBasis_apply ℝ L j, ← hfv,
        Module.Basis.ofZLatticeBasis_repr_apply]
    rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bV, ← hM, ← RingHom.map_det,
      eq_intCast]
  have hne : (LinearMap.det f).natAbs ≠ 0 := by
    intro h
    apply hdet
    rw [← hdetf, Int.natAbs_eq_zero.mp h, Int.cast_zero]
  let g : E →ₗ[ℤ] L ⧸ LinearMap.range f := (LinearMap.range f).mkQ ∘ₗ lam.rangeRestrict
  have hgs : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp lam.surjective_rangeRestrict
  have hkerg : LinearMap.ker g = LinearMap.range δ ⊔ Submodule.torsion ℤ E := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_sup, LinearMap.mem_range]
    constructor
    · rintro ⟨⟨_, z, rfl⟩, hz⟩
      refine ⟨δ z, ⟨z, rfl⟩, x - δ z, ?_, by abel⟩
      rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero]
      have := congrArg Subtype.val hz
      rw [hfv] at this
      simpa [hcomm] using this.symm
    · rintro ⟨_, ⟨z, rfl⟩, t, ht, rfl⟩
      rw [← hker, LinearMap.mem_ker] at ht
      refine ⟨lam.rangeRestrict z, Subtype.ext ?_⟩
      rw [hfv]
      simp [hcomm, ht]
  let e2 : (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) ≃ₗ[ℤ] L ⧸ LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hkerg.symm).trans (g.quotKerEquivOfSurjective hgs)
  haveI : Finite (L ⧸ LinearMap.range f) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  refine ⟨Finite.of_equiv _ e2.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e2.toEquiv, hcard, Nat.cast_natAbs, Int.cast_abs, hdetf]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Places

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.places :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsTotallyComplex F ∧ Fintype.card (InfinitePlace F) = orderOf γ * InfinitePlace.nrComplexPlaces L ∧ ∀ (k : ℕ) (w : InfinitePlace F), γ ^ k • w = w ↔ orderOf γ ∣ k := by
  intro L F _ _ _ _ _ γ hL hG hγ
  haveI := hL
  haveI : IsTotallyComplex F := isTotallyComplex_of_algebra L F
  haveI : IsUnramifiedAtInfinitePlaces L F :=
    ⟨fun w => InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))⟩
  have htop : Subgroup.zpowers γ = ⊤ := eq_top_iff.mpr fun σ _ => hγ σ
  have hcard : Module.finrank L F = orderOf γ := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, htop, Subgroup.card_top]
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace L F, hcard,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
  · intro k w
    have hst := (InfinitePlace.isUnramified L w).stabilizer_eq_bot
    rw [orderOf_dvd_iff_pow_eq_one, ← MulAction.mem_stabilizer_iff, hst, Subgroup.mem_bot]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ValuationUnitNeZero

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.V.ZK

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]

theorem valuation_unit_ne_zero (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) : P.valuation F (α : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 α.ne_zero

theorem valuation_eq_exp_ordP (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    P.valuation F (α : F) = WithZero.exp (-ordP P α) := by
  simp only [ordP, neg_neg]
  exact (WithZero.exp_log (valuation_unit_ne_zero P α)).symm

end UpperTheory.V.ZK

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ

section

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_prod (E : Type) [AddCommGroup E] (δ : Module.End ℤ E) (m : ℕ) :
    Nonempty (((E × ℤ) ⧸ (LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ))) ≃
      (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m) := by
  let φ : (E × ℤ) →ₗ[ℤ] (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m :=
    (Submodule.mkQ _).prodMap (Int.castAddHom (ZMod m)).toIntLinearMap
  have hs : Function.Surjective φ := fun ⟨x, y⟩ => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(x, y), rfl⟩
  have hk : LinearMap.ker φ =
      LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ) := by
    ext ⟨x, y⟩
    rw [LinearMap.mem_ker, Prod.ext_iff, Submodule.mem_sup]
    change (Submodule.Quotient.mk x = 0 ∧ (y : ZMod m) = 0) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, hr⟩, rfl⟩, k, rfl⟩
      exact ⟨_, ⟨(a, -k), rfl⟩, (t, 0), ⟨r, Prod.ext hr (by simp)⟩, by simp⟩
    · rintro ⟨_, ⟨⟨a, k⟩, rfl⟩, ⟨t, s⟩, ⟨r, hr⟩, h⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.1 hr
      have hs : s = 0 := (mul_eq_zero.1 (show (r : ℤ) * s = 0 from h4)).resolve_left (nonZeroDivisors.coe_ne_zero r)
      refine ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, h3⟩, h1⟩, -k, ?_⟩
      simpa [hs] using h2.symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk.symm).trans (φ.quotKerEquivOfSurjective hs)).toEquiv⟩

theorem UpperTheory.V.ZK.Ct.cardEQ :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsDat γ a D → Finite D.EQ ∧ Nat.card D.EQ * (a - 1) = (a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L := by
  intro L F _ _ _ _ _ γ a D hL hG hγ hD
  classical
  obtain ⟨hF, hc, hfree⟩ := places L F γ hL hG hγ
  have ha : 2 ≤ a := hD.a_eq ▸ D.two_le
  have hn : 0 < orderOf γ := hD.n_eq ▸ D.n_pos
  let ι : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive Fˣ :=
    (MonoidHom.toAdditive (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F))).toIntLinearMap
  have hι : Function.Injective ι := Units.map_injective RingOfIntegers.coe_injective
  have hr : LinearMap.range ι = LinearMap.ker D.d := by
    ext α
    obtain ⟨α, rfl⟩ := Additive.ofMul.surjective α
    have hv : D.d (Additive.ofMul α) = 0 ↔ ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F (α : F) = 1 := by
      rw [Finsupp.ext_iff]
      refine forall_congr' fun P => ?_
      rw [hD.d_eq, valuation_eq_exp_ordP, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]; rfl
    rw [LinearMap.mem_ker, hv]
    constructor
    · rintro ⟨u, hu⟩ P
      obtain rfl : Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u.toMul = α := hu
      refine le_antisymm (P.valuation_le_one (K := F) _) ?_
      have h1 := P.valuation_le_one (K := F) ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
      have h2 : P.valuation F (algebraMap (𝓞 F) F (u.toMul : (𝓞 F)ˣ)) *
          P.valuation F (algebraMap (𝓞 F) F ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      calc (1 : _) = _ := h2.symm
        _ ≤ _ * 1 := mul_le_mul_right h1 _
        _ = _ := mul_one _
    · intro h
      obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (α : F) fun P => (h P).le
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((α⁻¹ : Fˣ) : F) fun P => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h P, inv_one]
      have hxy : x * y = 1 := RingOfIntegers.coe_injective (by rw [map_mul, hx, hy, map_one, Units.mul_inv])
      exact ⟨Additive.ofMul (Units.mkOfMulEqOne x y hxy), Units.ext hx⟩
  let g : Module.End ℤ (Additive (𝓞 F)ˣ) := (MonoidHom.toAdditive (Units.map
    (RingOfIntegers.mapRingEquiv (γ⁻¹).toRingEquiv : 𝓞 F →* 𝓞 F))).toIntLinearMap
  let δ : Module.End ℤ (Additive (𝓞 F)ˣ) := g - (a : ℤ) • 1
  have hδ : ∀ u, ι (δ u) = D.del (ι u) := fun u => by
    have : ι (g u) = D.g (ι u) := by
      refine Eq.trans ?_ (hD.g_eq (ι u).toMul).symm
      exact congrArg Additive.ofMul (Units.ext rfl)
    simp only [δ, Dat.del, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_zsmul, this, hD.a_eq]
  let e : Additive (𝓞 F)ˣ ≃ₗ[ℤ] LinearMap.ker D.d := (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ u, (e u : Additive Fˣ) = ι u := fun _ => rfl
  have e2 : (Additive (𝓞 F)ˣ ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ _)) ≃ₗ[ℤ] D.EQ := by
    refine Submodule.Quotient.equiv _ _ e ?_
    ext y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, e.symm_apply_apply, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, he,
      Submodule.mem_sup, Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, t, ⟨r, ht⟩, rfl⟩
      refine ⟨_, ⟨ι v, hr ▸ ⟨v, rfl⟩, rfl⟩, ι t, ⟨r, ?_⟩, by rw [map_add (f := _), hδ]⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [← map_smul, ht, map_zero]
    · rintro ⟨_, ⟨v, hv, rfl⟩, t, ⟨r, ht⟩, h⟩
      rw [← hr] at hv
      obtain ⟨v, rfl⟩ := hv
      refine ⟨_, ⟨v, rfl⟩, u - δ v, ⟨r, hι ?_⟩, by abel⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [map_smul, map_sub, hδ, ← h, add_sub_cancel_left, ht, map_zero]
  let lam : Additive (𝓞 F)ˣ × ℤ →ₗ[ℤ] (InfinitePlace F → ℝ) := AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Real.log (w ((x.1.toMul : 𝓞 F) : F)) + x.2
      map_zero' := by ext w; simp
      map_add' := fun x y => by
        ext w
        simp only [Prod.fst_add, toMul_add, Units.val_mul, map_mul, Prod.snd_add, Int.cast_add, Pi.add_apply]
        rw [Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne']; ring }
  obtain ⟨u1, u2, u3⟩ := unitLat F hF lam fun _ _ _ => rfl
  have hdet := permDet (InfinitePlace F) (MulAction.toPerm γ) (orderOf γ) _ (a : ℝ) hn (by exact_mod_cast (by omega : 1 ≤ a)) hc
    fun k w => by rw [← hfree, ← MulAction.toPermHom_apply, ← map_pow]; rfl
  have h1 : (1 : ℝ) < (a : ℝ) ^ orderOf γ := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < a)) hn.ne'
  obtain ⟨f1, f2⟩ := latDet _ _ lam (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id))
    (LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) - (a : ℝ) • LinearMap.id) (by
      rintro ⟨u, m⟩
      have h2 : lam (g u, m) = LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) (lam (u, m)) := by
        ext w; rfl
      have h3 : (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id)) (u, m) = (g u, m) - (a : ℤ) • (u, m) := by
        refine Prod.ext rfl ?_
        simp only [LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Prod.snd_sub, Prod.smul_snd]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [h3, map_sub, h2, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul,
        Nat.cast_smul_eq_nsmul]) u1 u2 u3
    (by rw [← abs_pos, hdet]; exact pow_pos (by linarith) _)
  obtain ⟨e3⟩ := card_prod _ δ (a - 1)
  haveI : NeZero (a - 1) := ⟨by omega⟩
  have f3 := (e3.finite_iff).1 f1
  refine ⟨e2.toEquiv.finite_iff.1 (Finite.prod_left (ZMod (a - 1))), ?_⟩
  rw [Nat.card_congr e3, Nat.card_prod, Nat.card_zmod, Nat.card_congr e2.toEquiv, hdet] at f2
  have h4 : 1 ≤ a ^ orderOf γ := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast f2.trans (by rw [Nat.cast_pow, Nat.cast_sub h4]; push_cast; rfl :
    ((a : ℝ) ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L = (((a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L : ℕ) : ℝ))
end
end
