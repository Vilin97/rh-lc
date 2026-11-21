import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

private theorem ext_proper {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B)
    (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

private theorem alg_map {K R C : Type} [Field K] [Field R] [CharZero R] [Field C] [Algebra R C] (k : K →+* C) (a : K)
    (h : IsAlgebraic ℤ a) : IsAlgebraic R (k a) :=
  (h.algHom k.toIntAlgHom).extendScalars (S := R) Int.cast_injective

private theorem int_map {A R C : Type} [CommRing A] [CommRing R] [CommRing C] [Algebra R C] (k : A →+* C) (a : A)
    (h : IsIntegral ℤ a) : IsIntegral R (k a) :=
  (h.map k.toIntAlgHom).tower_top

private theorem norm_le_one_of_isIntegral (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (h1 : IsIntegral 𝓞_ℂ_[p] x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : Valued.v (y : ℂ_[p]) ≤ 1 := y.2
  rw [← GlobalTheory.FlatModel.coe_valued]
  exact NNReal.coe_le_one.mpr h2

private theorem descend_gen (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)) (hs : IsProper s)
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (k : K →+* ℂ_[p]) (z : Sp K ⟶ X) (hK : ∀ a : K, IsAlgebraic ℤ a) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO ≫ yT = spMap k ≫ z := by
  let T : CDVR := { V := ℤ_[p] }
  have hfin : T.FinRes := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  let g : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have hg : Function.Injective g := (algebraMap ℚ_[p] ℂ_[p]).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  have hgO : ∀ a, g a ∈ 𝓞_ℂ_[p] := fun a => by
    show Valued.v (g a) ≤ 1
    rw [← NNReal.coe_le_one, GlobalTheory.FlatModel.coe_valued]
    show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  let kO : T.V →+* 𝓞_ℂ_[p] := g.codRestrict (𝓞_ℂ_[p]) hgO
  let kk : T.Fr →+* ℂ_[p] := IsFractionRing.lift (K := FractionRing ℤ_[p]) hg
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kk (algebraMap T.V T.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap (K := FractionRing ℤ_[p]) hg a).symm
  letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra
  let K' : IntermediateField T.Fr ℂ_[p] := algebraicClosure T.Fr ℂ_[p]
  have hKa : Algebra.IsAlgebraic T.Fr K' := algebraicClosure.isAlgebraic T.Fr ℂ_[p]
  haveI : CharZero T.Fr := RingHom.charZero kk
  have hkK : ∀ a, k a ∈ K' := fun a => by
    rw [mem_algebraicClosure_iff]
    exact alg_map k a (hK a)
  let k' : K →+* K' := k.codRestrict K' hkK
  have hft : LocallyOfFiniteType (s ≫ spMap (algebraMap ℤ (𝓞 F))) := by
    have : LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 F))) := by
      unfold spMap
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    infer_instance
  obtain ⟨L, yL, hLfin, hyL1, -⟩ := GlobalTheory.FinDesc.exists_finite_subext_point _ _ _ hft T.Fr K' hKa (spMap k' ≫ z)
    (spMap (algebraMap ℤ T.Fr)) (specZIsTerminal.hom_ext _ _)
  obtain ⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K'.val.toRingHom.comp L.val.toRingHom := ⟨_, rfl⟩
  have hkL1 : ∀ x : L, kL x = ((x : K') : ℂ_[p]) := fun x => by rw [hkL]; rfl
  obtain ⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩ :=
    GlobalTheory.CdvrLiftCp.exists_cdvr_lift p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (yL ≫ s : Sp L ⟶ Sp (𝓞 F))
  obtain ⟨fL, hfLφ⟩ : ∃ fL : 𝓞 F →+* L, fL = φ.hom := ⟨_, rfl⟩
  have hφ' : yL ≫ s = spMap fL := by rw [← hφ, hfLφ]; rfl
  obtain ⟨β', hβ'⟩ := hint (𝓞 F) fL (fun a => norm_le_one_of_isIntegral p _
    (int_map (kL.comp fL) a (RingOfIntegers.isIntegral a)))
  have hring : ψ.toRingHom.comp fL = (algebraMap T'.V T'.Fr).comp β' := RingHom.ext fun a => (hβ' a).symm
  have hsq : (spMap ψ.toRingHom ≫ yL) ≫ s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β' := by
    rw [Category.assoc, hφ', spMap_spMap, spMap_spMap, hring]
  obtain ⟨yT, hyT⟩ := ext_proper s hs (spMap ψ.toRingHom ≫ yL) (spMap β') hsq
  refine ⟨T', kO', yT, hT'fin, hkO'inj, ?_⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = (kL.comp ψ.symm.toRingHom).comp (algebraMap T'.V T'.Fr) :=
    RingHom.ext hkO'
  have e1 : (kL.comp ψ.symm.toRingHom).comp ψ.toRingHom = K'.val.toRingHom.comp (algebraMap L K') :=
    RingHom.ext fun x => by
      show kL (ψ.symm (ψ x)) = _
      rw [RingEquiv.symm_apply_apply, hkL1]; rfl
  have e2 : K'.val.toRingHom.comp k' = k := RingHom.ext fun _ => rfl
  rw [← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, ← Category.assoc, spMap_spMap, e1,
    ← spMap_spMap, Category.assoc, hyL1, ← Category.assoc, spMap_spMap, e2]

private theorem descend (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)) (hs : IsProper s)
    (p : ℕ) [Fact p.Prime] (yb : Sp 𝓞_ℂ_[p] ⟶ X) (K : Type) [Field K] (k : K →+* ℂ_[p]) (z : Sp K ⟶ X)
    (hK : ∀ a : K, IsAlgebraic ℤ a) (hz : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = spMap k ≫ z) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap kO ≫ yT = yb := by
  obtain ⟨T, kO, yT, h1, h2, h3⟩ := descend_gen F X s hs p K k z hK
  refine ⟨T, kO, yT, h1, h2, ?_⟩
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  haveI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  haveI : IsDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap 𝓞_ℂ_[p] ℂ_[p])).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hiO]; exact bot_le)⟩
  exact ext_of_isDominant (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) (h3.trans hz.symm)

private theorem lift_gen {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {K C : Type} [Field K] [Field C] (k : K →+* C)
    (x : Sp K ⟶ Z.X) (yy : Sp C ⟶ Xo.XF c) (h : spMap k ≫ x = yy ≫ Z.j) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = x ∧ spMap k ≫ y = yy := by
  have h' : spMap k ≫ x = yy ≫ Z.jQ ≫ Limits.pullback.fst _ _ := h
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 c.F →+* K, x ≫ Z.s = spMap b :=
    ⟨(Spec.preimage (x ≫ Z.s)).hom, (Spec.map_preimage (x ≫ Z.s)).symm⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : c.F →+* C, yy ≫ Z.jQ ≫ Limits.pullback.snd _ _ = spMap g₀ :=
    ⟨(Spec.preimage (yy ≫ Z.jQ ≫ Limits.pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have e0 : k.comp b = g₀.comp (algebraMap (𝓞 c.F) c.F) := by
    have e : spMap (k.comp b) = spMap (g₀.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← spMap_spMap, ← spMap_spMap, ← hb, ← hg₀, reassoc_of% h', Limits.pullback.condition]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hbi : Function.Injective b := by
    have : Function.Injective (k.comp b) := by
      rw [e0]
      exact g₀.injective.comp (IsFractionRing.injective (𝓞 c.F) c.F)
    exact Function.Injective.of_comp (f := k) this
  let g : c.F →+* K := IsFractionRing.lift hbi
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = b := RingHom.ext fun a => IsFractionRing.lift_algebraMap hbi a
  have hkg : k.comp g = g₀ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by rw [RingHom.comp_assoc, hg, e0])
  have hw : x ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [spMap_spMap, hg, hb]
  let yK : Sp K ⟶ Limits.pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := Limits.pullback.lift x (spMap g) hw
  have hyK : spMap k ≫ yK = yy ≫ Z.jQ := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, h', Category.assoc]
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.assoc, hg₀, spMap_spMap, hkg]
  have hr : Set.range yK ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨q0⟩ : Nonempty (Sp C) := inferInstance
    have hq : q = spMap k q0 := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hq, ← Scheme.Hom.comp_apply, hyK, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  haveI := Z.jQ_open
  have hy' : IsOpenImmersion.lift Z.jQ yK hr ≫ Z.jQ = yK := IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift Z.jQ yK hr, ?_, ?_⟩
  · show _ ≫ Z.jQ ≫ Limits.pullback.fst _ _ = _
    rw [← Category.assoc, hy', Limits.pullback.lift_fst]
  · rw [← cancel_mono Z.jQ, Category.assoc, hy', hyK]
