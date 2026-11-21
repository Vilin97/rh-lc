module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.CardSUnit

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_valuationSubring_isPlaceOver (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ A : ValuationSubring Ω, IsPlaceOver A v := by
  let f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let e : 𝓞 K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := v.asIdeal.map e
  have hI : I ≠ ⊤ := by
    haveI : (v.asIdeal.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    exact Ideal.IsPrime.ne_top this
  obtain ⟨V, hRV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hlt : ∀ y ∈ v.asIdeal, V.valuation (f y) < 1 := by
    intro y hy
    have h1 : f y ∈ V.nonunits := hV ⟨e y, Ideal.mem_map_of_mem e hy, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).1 h1
  have hle : ∀ y : 𝓞 K, V.valuation (f y) ≤ 1 := by
    intro y
    exact (ValuationSubring.valuation_le_one_iff V _).2 (hRV (RingHom.mem_range_self f y))
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hlt x hx⟩⟩
  by_contra hxv
  obtain ⟨r, y, hy, hry⟩ := v.isMaximal.exists_inv hxv
  have h2 : V.valuation (f (r * x)) < 1 := by
    rw [map_mul, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle r)) hx
  have h3 : V.valuation (f (r * x + y)) < 1 := by
    rw [map_add (f := _)]
    exact Valuation.map_add_lt _ h2 (hlt y hy)
  rw [hry, map_one, Valuation.map_one] at h3
  exact lt_irrefl _ h3

private theorem finite_above_of_ne_zero (K : Type) [Field K] [NumberField K] (N : ℕ) (hN : N ≠ 0) :
    (Above (F := K) N).Finite := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

theorem UpperTheory.V.Kum.finChar :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n N : ℕ) (ζ : K), n ≠ 0 → N ≠ 0 → IsPrimitiveRoot ζ n → {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}.Finite := by
  intro K Ω _ _ _ _ _ n N ζ hn hN hζ
  haveI : NeZero n := ⟨hn⟩
  let ζΩ := algebraMap K Ω ζ
  have hζΩ : IsPrimitiveRoot ζΩ n := hζ.map_of_injective (algebraMap K Ω).injective
  have hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x :=
    fun g x => AlgEquiv.commutes g x
  have hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val := by
    intro g
    rw [hfix g ζ]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
    · have hn1 : n = 1 := by omega
      subst hn1
      have : ζΩ = 1 := IsPrimitiveRoot.one_right_iff.1 hζΩ
      show ζΩ = ζΩ ^ _
      rw [this, one_pow]
  have key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0},
      ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above (F := K) N) n ∧ β ^ n = algebraMap K Ω a ∧
        ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by
    rintro φ ⟨hlc, hadd, hine⟩
    obtain ⟨β, a, hβ, hg⟩ := radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc
      (fun g h => by rw [hadd, one_mul])
    refine ⟨β, a, ?_, hβ, hg⟩
    intro v hv
    obtain ⟨A, hA⟩ := exists_valuationSubring_isPlaceOver K Ω v
    have hnot : ¬ A.valuation (N : Ω) < 1 := by
      intro h
      have hcast : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
      rw [← hcast] at h
      exact hv ((hA (N : 𝓞 K)).1 h)
    exact dvdOfIne K Ω n A v β a hA hβ
      (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])
  choose! β a ha hβ hg using key
  let S := Above (F := K) N
  have : Finite S := finite_above_of_ne_zero K N hN
  have : Finite (SelK S n ⧸ (powK (K := K) n).subgroupOf (SelK S n)) := by
    let P := powK (K := K) n
    let U := S.unit K
    let f : SelK S n →* ClS S := MonoidHom.mk'
      (fun a => QuotientGroup.mk (radCl n a.1))
      (fun a b => (radClMul K S n hn).1 a.1 a.2 b.1 b.2)
    have mem_unit_iff (u : Kˣ) : u ∈ U ↔ ∀ v ∉ S, ordv v u = 0 := by
      change (∀ v ∉ S, v.valuation K (u : K) = 1) ↔ _
      refine forall₂_congr fun v _ => ?_
      rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj,
        ordv, neg_eq_zero, toAdd_eq_zero]
    have hU : U ≤ SelK S n := by
      intro a ha v hv
      rw [(mem_unit_iff a).1 ha v hv]
      exact dvd_zero _
    have hP : P ≤ SelK S n := by
      rintro _ ⟨b, rfl⟩ v _
      simp [ordv]
    have hker : f.ker ≤ (U ⊔ P).subgroupOf (SelK S n) := by
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      change (QuotientGroup.mk (radCl n a.1) : ClS S) = 1 at ha
      rw [QuotientGroup.eq_one_iff] at ha
      classical
      have finite_add {d e : HeightOneSpectrum (𝓞 K) → ℤ}
          (hd : {v | d v ≠ 0}.Finite) (he : {v | e v ≠ 0}.Finite) :
          {v | d v + e v ≠ 0}.Finite := by
        refine (hd.union he).subset ?_
        intro v hv
        by_contra h
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
        exact hv (by rw [h.1, h.2, add_zero])
      have prod_add {d e : HeightOneSpectrum (𝓞 K) → ℤ}
          (hd : {v | d v ≠ 0}.Finite) (he : {v | e v ≠ 0}.Finite) :
          ∏ᶠ v, primeCl v ^ (d v + e v) = (∏ᶠ v, primeCl v ^ d v) * ∏ᶠ v, primeCl v ^ e v := by
        rw [← finprod_mul_distrib]
        · exact finprod_congr fun v => zpow_add _ _ _
        · exact hd.subset fun v hv h => hv (by simp [h])
        · exact he.subset fun v hv h => hv (by simp [h])
      have supported {c : ClassGroup (𝓞 K)} (hc : c ∈ clSub S) :
          ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
            c = ∏ᶠ v, primeCl v ^ g v := by
        induction hc using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨w, hw, rfl⟩ := hx
          refine ⟨fun v => if v = w then 1 else 0, (Set.finite_singleton w).subset ?_,
            fun v hv => ite_eq_right fun (h : v = w) => hv (h ▸ hw), ?_⟩
          · intro v hv
            by_contra h
            exact hv (ite_eq_right h)
          · rw [finprod_eq_single _ w fun v hv => by simp [hv]]
            simp
        | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
        | mul x y _ _ hx hy =>
          obtain ⟨d, hd, hdS, rfl⟩ := hx
          obtain ⟨e, he, heS, rfl⟩ := hy
          exact ⟨fun v => d v + e v, finite_add hd he, fun v hv => by simp [hdS v hv, heS v hv],
            (prod_add hd he).symm⟩
        | inv x _ hx =>
          obtain ⟨d, hd, hdS, rfl⟩ := hx
          refine ⟨fun v => -d v, by simpa using hd, fun v hv => by simp [hdS v hv], ?_⟩
          rw [← finprod_inv_distrib]
          exact finprod_congr fun v => (zpow_neg _ _).symm
      obtain ⟨g, hg, hgS, hclass⟩ := supported (inv_mem ha)
      obtain ⟨mk_eq_prod, count_eq_ordv, finite_ordv, _⟩ := clProd K
      have hdiv : {v | ordv v a.1 / (n : ℤ) ≠ 0}.Finite :=
        (finite_ordv a.1).subset fun v hv h => hv (by simp [h])
      let d (v : HeightOneSpectrum (𝓞 K)) : ℤ := ordv v a.1 / n + g v
      have hd : {v | d v ≠ 0}.Finite := finite_add hdiv hg
      have hdClass : ∏ᶠ v, primeCl v ^ d v = 1 := by
        change (∏ᶠ v, primeCl v ^ (ordv v a.1 / (n : ℤ) + g v)) = 1
        rw [prod_add hdiv hg, ← hclass]
        exact mul_inv_cancel _
      let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ d v
      have hI0 : I ≠ 0 := by
        refine finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
        exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
      have hcount (v : HeightOneSpectrum (𝓞 K)) : FractionalIdeal.count K v I = d v :=
        FractionalIdeal.count_finprod K v d (by simpa [Filter.eventually_cofinite] using hd)
      have hIClass : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
        rw [mk_eq_prod, ← hdClass]
        exact finprod_congr fun v => by rw [Units.val_mk0, hcount]
      obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 hIClass)
      rw [Units.val_mk0] at hb
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact hI0 (by rw [hb, map_zero])
      let u := Units.mk0 b hb0
      have hu (v : HeightOneSpectrum (𝓞 K)) : ordv v u = d v := by
        rw [← count_eq_ordv, show (u : K) = b from rfl, ← hb, hcount]
      refine Subgroup.mem_sup.2 ⟨a.1 * (u ^ n)⁻¹, (mem_unit_iff _).2 fun v hv => ?_,
        u ^ n, ⟨u, rfl⟩, by simp⟩
      have hpow_v : ordv v (u ^ n) = n * ordv v u := by simp [ordv]
      rw [ordv_mul, ordv_inv, hpow_v, hu, show d v = ordv v a.1 / n + g v from rfl,
        hgS v hv, add_zero, Int.mul_ediv_cancel' (a.2 v hv), add_neg_cancel]
    have : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, inferInstance⟩
    have : (powMonoidHom n : U →* U).range.FiniteIndex := by
      refine ⟨?_⟩
      rw [GroundTheory.Global.SUnit.index_range_powMonoidHom S n]
      exact pow_ne_zero _ hn
    have : (P.subgroupOf U).FiniteIndex := Subgroup.finiteIndex_of_le
      (show (powMonoidHom n : U →* U).range ≤ P.subgroupOf U from by
        rintro _ ⟨u, rfl⟩
        exact ⟨u.1, rfl⟩)
    have : ((U ⊔ P).subgroupOf (SelK S n)).FiniteIndex := Subgroup.finiteIndex_of_le hker
    apply Subgroup.index_ne_zero_iff_finite.1
    have hUP : U ⊔ P ≤ SelK S n := sup_le hU hP
    have hle : P.subgroupOf (SelK S n) ≤ (U ⊔ P).subgroupOf (SelK S n) :=
      fun _ ha => (le_sup_right : P ≤ U ⊔ P) ha
    rw [← Subgroup.relIndex_mul_index hle, Subgroup.relIndex_subgroupOf hUP,
      Subgroup.relIndex_sup_right]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := SelK S n ⧸ (powK (K := K) n).subgroupOf (SelK S n))
    (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
  simp only at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hcu : a φ * c ^ n = a ψ := by rw [hc, mul_inv_cancel_left]
  have hne : ∀ θ ∈ _, β θ ≠ 0 := fun θ hθ h0 => by
    have := hβ θ hθ
    rw [h0, zero_pow hn] at this
    exact (Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))
  refine Subtype.ext (funext fun g => ?_)
  have hφ0 := hne φ hφ
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact c.ne_zero
  set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef
  have hωn : ω ^ n = 1 := by
    rw [hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]
    push_cast
    exact div_self (by simp)
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hωn
  have hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K)) := by
    rw [hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]
  have hgω : g ω = ω := by
    rw [← hi, map_pow]
    exact congrArg (· ^ i) (hfix g ζ)
  have hω0 : ω ≠ 0 := by
    rw [← hi]
    exact pow_ne_zero _ (hζΩ.ne_zero hn)
  have e1 := hg ψ hψ g
  rw [hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix] at e1
  have e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val := by
    have h3 := mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ)
    apply mul_right_cancel₀ h3
    linear_combination e1
  exact ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)
