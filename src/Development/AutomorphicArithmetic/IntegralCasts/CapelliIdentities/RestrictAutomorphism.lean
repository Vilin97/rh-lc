module

public import Mathlib

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.RestrictAutomorphism.zlW :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → (R : Type) → [inst_1 : CommRing R] → [CharP R l] → ℤ_[l] →+* WittVector l R :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (R : Type) [CommRing R] [CharP R l] ↦
      (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom

namespace UpperTheory.Reformulated.B.RestrictAutomorphism

private theorem hom_unique {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (φ ψ : ℤ_[p] →+* WittVector p R) : φ = ψ := by
  ext1 x
  rw [← sub_eq_zero]
  ext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (i + 1) x)
  have hx : x = y * (p : ℤ_[p]) ^ (i + 1) + (x.appr (i + 1) : ℤ_[p]) := by
    rw [hy]; ring
  have h : φ x - ψ x = (φ y - ψ y) * (p : WittVector p R) ^ (i + 1) := by
    conv_lhs => rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self i), WittVector.zero_coeff]

private theorem pow_pow_mul {p : ℕ} {R : Type} [CommRing R] {y : R} {m : ℕ}
    (h : y ^ p ^ m = y) (n : ℕ) : y ^ p ^ (m * n) = y := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private def algPart (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m : ℕ, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  mul_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  neg_mem' := by
    rintro a ⟨m, hm, ha⟩
    refine ⟨m, hm, ?_⟩
    have h := map_neg (iterateFrobenius R p m) a
    rwa [iterateFrobenius_def, iterateFrobenius_def, ha] at h

private theorem map_mem_algPart {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) {y : R} (hy : y ∈ algPart p R) : σ y ∈ algPart p R := by
  obtain ⟨m, hm, h⟩ := hy
  exact ⟨m, hm, by rw [← map_pow, h]⟩

private def restrictAut (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) : algPart p R ≃+* algPart p R where
  toFun y := ⟨σ y, map_mem_algPart σ y.2⟩
  invFun y := ⟨σ.symm y, map_mem_algPart σ.symm y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv y := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ (a : R) b)
  map_add' a b := Subtype.ext (map_add σ (a : R) b)

private def restrictHom (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    [CharP R p] (ρ : G →* R ≃+* R) : G →* algPart p R ≃+* algPart p R where
  toFun g := restrictAut p (ρ g)
  map_one' := by
    ext y
    show ρ 1 (y : R) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    show ρ (g * h) (y : R) = ρ g (ρ h y)
    rw [map_mul]; rfl

-- The descent argument from NormSubgroupOpen is local because that file uses legacy imports.
private lemma sum_shift {G : Type} [Group G] (N : Subgroup G) [Fintype (G ⧸ N)] {X : Type}
    [AddCommMonoid X] (F : G → X) (hF : ∀ g, ∀ ν ∈ N, F (g * ν) = F g) (h : G) :
    ∑ q : G ⧸ N, F (h * q.out) = ∑ q : G ⧸ N, F q.out := by
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ fun q => ?_
  obtain ⟨ν, hν⟩ := QuotientGroup.mk_out_eq_mul N (h * q.out)
  have : (MulAction.toPerm h) q = ((h * q.out : G) : G ⧸ N) := by
    have := MulAction.Quotient.mk_smul_out N h q
    simpa using this.symm
  rw [this, hν, hF _ _ ν.2]

private lemma avg {G A C : Type} [Group G] [CommRing A] [CommRing C] {r : ℕ}
    (σ : G → A →+* A) (hσ : ∀ g h x, σ (g * h) x = σ g (σ h x))
    (P : G → Matrix (Fin r) (Fin r) A) (hP : ∀ g h, P (g * h) = P g * P h)
    (hfix : ∀ g h, (P h).map (σ g) = P h) (τ : A →+* C) (N : Subgroup G) [Fintype (G ⧸ N)]
    (hN : ∀ ν ∈ N, (P ν).map τ = 1) (B : Matrix (Fin r) (Fin r) A)
    (hB : ∀ ν ∈ N, B.map (σ ν) = B) (h : G) :
    (P h * (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map (σ h)).map τ
      = (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map τ := by
  have hm : ∀ g k, B.map (σ (g * k)) = (B.map (σ k)).map (σ g) := by
    intro g k; ext i j; simp [hσ]
  have h1 : P h * (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map (σ h)
      = ∑ q : G ⧸ N, P (h * q.out) * B.map (σ (h * q.out)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingHom.mapMatrix_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hfix, hP, hm, Matrix.mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_sum, map_sum]
  refine sum_shift N (fun g => τ.mapMatrix (P g * B.map (σ g))) (fun g ν hν => ?_) h
  simp only [RingHom.mapMatrix_apply]
  rw [hm, hB ν hν, hP, Matrix.map_mul, Matrix.map_mul, hN ν hν, Matrix.mul_one, Matrix.map_mul]

private lemma dedekind {T L Q : Type} [CommRing T] [CommRing L] [IsDomain L] [Fintype Q]
    (χ : Q → T →+* L) (hχ : Function.Injective χ) (c : Q → L)
    (hc : ∀ a, ∑ q, c q * χ q a = 0) (q : Q) : c q = 0 := by
  have hinj : Function.Injective (fun q => (χ q).toMonoidHom) := by
    intro a b hab
    apply hχ
    ext x
    exact DFunLike.congr_fun hab x
  have := (linearIndependent_monoidHom T L).comp _ hinj
  rw [Fintype.linearIndependent_iff] at this
  apply this c
  funext a
  simpa [Finset.sum_apply] using hc a

private lemma det_field {T L Q : Type} [CommRing T] [Field L] [Fintype Q] {r : ℕ}
    (χ : Q → T →+* L) (hχ : Function.Injective χ) (P : Q → Matrix (Fin r) (Fin r) L)
    (q0 : Q) (P' : Matrix (Fin r) (Fin r) L) (hP : P q0 * P' = 1) :
    ∃ B : Matrix (Fin r) (Fin r) T, (∑ q, P q * B.map (χ q)).det ≠ 0 := by
  classical
  let v : (Fin r → T) → (Fin r → L) := fun x => ∑ q, (P q).mulVec (χ q ∘ x)
  have hspan : Submodule.span L (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hcol : ∀ j, f ((P q0).mulVec (Pi.single j 1)) = 0 := by
      intro j
      refine dedekind χ hχ (fun q => f ((P q).mulVec (Pi.single j 1))) (fun a => ?_) q0
      have h1 : f (v (Pi.single j a)) = 0 :=
        hf (Submodule.subset_span ⟨_, rfl⟩)
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : (χ q ∘ (Pi.single j a : Fin r → T)) = χ q a • (Pi.single j 1 : Fin r → L) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [this, Matrix.mulVec_smul, map_smul, smul_eq_mul, mul_comm]
    apply hf0
    refine LinearMap.ext fun w => ?_
    have hw : w = (P q0).mulVec (P'.mulVec w) := by
      rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
    rw [hw]
    generalize P'.mulVec w = u
    have hu : u = ∑ j, u j • (Pi.single j 1 : Fin r → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu, Matrix.mulVec_sum, map_sum]
    simp only [Matrix.mulVec_smul, map_smul, hcol]
    simp
  have hex : ∃ f : Fin r → (Fin r → L), (∀ i, f i ∈ Set.range v) ∧ LinearIndependent L f := by
    obtain ⟨f, h1, -, h3⟩ := Submodule.exists_fun_fin_finrank_span_eq L (Set.range v)
    have hr : Module.finrank L (Submodule.span L (Set.range v)) = r := by
      rw [hspan]; simp
    exact ⟨f ∘ Fin.cast hr.symm, fun i => h1 _, h3.comp _ (Fin.cast_injective _)⟩
  obtain ⟨f, h1, h2⟩ := hex
  choose x hx using h1
  refine ⟨Matrix.of fun i j => x j i, ?_⟩
  have : (∑ q, P q * (Matrix.of fun i j => x j i).map (χ q)).col = f := by
    funext j i
    rw [← hx j]
    simp [v, Matrix.col, Matrix.sum_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Finset.sum_apply]
  rw [← this, Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h2
  exact h2.ne_zero

private lemma det_domain {T R Q : Type} [CommRing T] [CommRing R] [IsDomain R] [Fintype Q] {r : ℕ}
    (χ : Q → T →+* R) (hχ : Function.Injective χ) (P : Q → Matrix (Fin r) (Fin r) R)
    (q0 : Q) (P' : Matrix (Fin r) (Fin r) R) (hP : P q0 * P' = 1) :
    ∃ B : Matrix (Fin r) (Fin r) T, (∑ q, P q * B.map (χ q)).det ≠ 0 := by
  let ι := algebraMap R (FractionRing R)
  have hι : Function.Injective ι := IsFractionRing.injective R (FractionRing R)
  obtain ⟨B, hB⟩ := det_field (fun q => ι.comp (χ q)) (fun a b hab => hχ (by
      ext x; exact hι (DFunLike.congr_fun hab x))) (fun q => (P q).map ι) q0 (P'.map ι) (by
      rw [← Matrix.map_mul, hP]; simp)
  refine ⟨B, fun h => hB ?_⟩
  have : (∑ q, (P q).map ι * B.map (ι.comp (χ q))) = ι.mapMatrix (∑ q, P q * B.map (χ q)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_mul]; rfl
  rw [this, ← RingHom.map_det, h, map_zero]

section
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [Group G] {R : Type} [CommRing R]

private def Nm (ρ : G →* R ≃+* R) (p m : ℕ) : Subgroup G where
  carrier := {g | ∀ y : R, y ^ p ^ m = y → ρ g y = y}
  mul_mem' := by
    intro a b ha hb y hy
    rw [map_mul]
    change ρ a (ρ b y) = y
    rw [hb y hy, ha y hy]
  one_mem' := by intro y _; rw [map_one]; rfl
  inv_mem' := by
    intro a ha y hy
    have : ρ a⁻¹ (ρ a y) = y := by
      change (ρ a⁻¹ * ρ a) y = y
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rwa [ha y hy] at this

private noncomputable def sg (p : ℕ) [Fact (Nat.Prime p)] (ρ : G →* R ≃+* R) (g : G) :
    WittVector p R →+* WittVector p R := WittVector.map (ρ g).toRingHom

private lemma sg_coeff (ρ : G →* R ≃+* R) (g : G) (x : WittVector p R) (i : ℕ) :
    (sg p ρ g x).coeff i = ρ g (x.coeff i) := by
  simp [sg, WittVector.map_coeff]

private lemma sg_mul (ρ : G →* R ≃+* R) (g h : G) (x : WittVector p R) :
    sg p ρ (g * h) x = sg p ρ g (sg p ρ h x) := by
  ext i; simp [sg_coeff]

private lemma trunc_iff (n : ℕ) (x y : WittVector p R) :
    WittVector.truncate n x = WittVector.truncate n y ↔ ∀ i < n, x.coeff i = y.coeff i := by
  constructor
  · intro h i hi
    rw [← WittVector.coeff_truncate x ⟨i, hi⟩, ← WittVector.coeff_truncate y ⟨i, hi⟩, h]
  · intro h
    ext i
    simp [WittVector.coeff_truncate, h i i.2]

variable [CharP R p]

private lemma map_zl (f : R →+* R) (x : ℤ_[p]) : WittVector.map f (zlW p R x) = zlW p R x := by
  ext i
  simp only [zlW, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) R))
    (ZMod.castHom (dvd_refl p) R)) _

private noncomputable def Sm (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    (m : ℕ) : Subring (WittVector p R) :=
  (WittVector.map (iterateFrobenius R p m)).eqLocus (RingHom.id _)

private noncomputable def Km (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    (m : ℕ) : Subring R :=
  (iterateFrobenius R p m).eqLocus (RingHom.id _)

private lemma mem_Km (m : ℕ) (y : R) : y ∈ Km p R m ↔ y ^ p ^ m = y := by
  simp [Km, iterateFrobenius_def]

private lemma mem_Sm' (m : ℕ) (x : WittVector p R) :
    x ∈ Sm p R m ↔ WittVector.map (iterateFrobenius R p m) x = x := Iff.rfl

private lemma mem_Sm (m : ℕ) (x : WittVector p R) :
    x ∈ Sm p R m ↔ ∀ i, x.coeff i ^ p ^ m = x.coeff i := by
  rw [mem_Sm', WittVector.ext_iff]
  simp [WittVector.map_coeff, iterateFrobenius_def]

private lemma zl_mem (m : ℕ) (x : ℤ_[p]) : zlW p R x ∈ Sm p R m := map_zl _ x

private lemma sg_mem (ρ : G →* R ≃+* R) (g : G) {m : ℕ} {x : WittVector p R} (h : x ∈ Sm p R m) :
    sg p ρ g x ∈ Sm p R m := by
  rw [mem_Sm] at h ⊢
  intro i
  rw [sg_coeff, ← map_pow, h]

private lemma sg_fix (ρ : G →* R ≃+* R) {g : G} {m : ℕ} (hg : g ∈ Nm ρ p m) {x : WittVector p R}
    (h : x ∈ Sm p R m) : sg p ρ g x = x := by
  rw [mem_Sm] at h
  ext i
  rw [sg_coeff, hg _ (h i)]

private lemma teich_mem {m : ℕ} {a : R} (ha : a ^ p ^ m = a) :
    WittVector.teichmuller p a ∈ Sm p R m := by
  rw [mem_Sm', WittVector.map_teichmuller, iterateFrobenius_def, ha]

private lemma unit_of_coeff {x : WittVector p R} (h : IsUnit (x.coeff 0)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  exact ⟨WittVector.mkUnit hu.symm, WittVector.coe_mkUnit _⟩

variable [IsDomain R]

omit [CharP R p] in
private lemma unit_of_per {m : ℕ} (hm : 0 < m) {y : R} (hy : y ^ p ^ m = y) (h0 : y ≠ 0) :
    IsUnit y := by
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  obtain ⟨k, hk⟩ : ∃ k, p ^ m = k + 2 := ⟨p ^ m - 2, by omega⟩
  rw [hk] at hy
  have : y * y ^ k = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    conv_rhs => rw [← hy]
    ring
  exact IsUnit.of_mul_eq_one _ this

private noncomputable def chi (ρ : G →* R ≃+* R) (p : ℕ) [Fact (Nat.Prime p)] [CharP R p] (m : ℕ)
    (q : G ⧸ Nm ρ p m) : Km p R m →+* R := (ρ q.out).toRingHom.comp (Km p R m).subtype

omit [IsDomain R] in
private lemma chi_apply (ρ : G →* R ≃+* R) (m : ℕ) (q : G ⧸ Nm ρ p m) (a : Km p R m) :
    chi ρ p m q a = ρ q.out a := rfl

omit [IsDomain R] in
private lemma chi_inj (ρ : G →* R ≃+* R) (m : ℕ) : Function.Injective (chi ρ p m) := by
  intro a b hab
  rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, QuotientGroup.eq]
  intro y hy
  have := DFunLike.congr_fun hab ⟨y, (mem_Km m y).2 hy⟩
  simp only [chi_apply] at this
  rw [map_mul]
  change ρ a.out⁻¹ (ρ b.out y) = y
  rw [← this]
  change (ρ a.out⁻¹ * ρ a.out) y = y
  rw [← map_mul, inv_mul_cancel, map_one]; rfl

private lemma free_etale_sheaf_zmod_exists_hom_sending_generator (ρ : G →* R ≃+* R) {m : ℕ} (hm : 0 < m) [Fintype (G ⧸ Nm ρ p m)] :
    ∃ t ∈ Sm p R m, ∑ q : G ⧸ Nm ρ p m, sg p ρ q.out t = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : Km p R m, ∑ q : G ⧸ Nm ρ p m, (1 : R) * chi ρ p m q a ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero (dedekind (chi ρ p m) (chi_inj ρ m) (fun _ => (1 : R)) h ((1 : G) : _))
  have hT : WittVector.teichmuller p (a : R) ∈ Sm p R m := teich_mem ((mem_Km m _).1 a.2)
  set T := WittVector.teichmuller p (a : R) with hTd
  set s := ∑ q : G ⧸ Nm ρ p m, sg p ρ q.out T with hs
  have hsS : s ∈ Sm p R m := Subring.sum_mem _ fun q _ => sg_mem ρ _ hT
  have hs0 : s.coeff 0 ≠ 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← WittVector.constantCoeff_apply, hs, map_sum]
    simpa [sg_coeff, hTd, chi_apply] using ha
  obtain ⟨u, hu⟩ : IsUnit s := unit_of_coeff (unit_of_per hm ((mem_Sm m s).1 hsS 0) hs0)
  have hinv : ∀ φ : WittVector p R →+* WittVector p R, φ s = s → φ (↑u⁻¹) = ↑u⁻¹ := by
    intro φ hφ
    have h1 : s * φ (↑u⁻¹) = 1 := by
      rw [← hφ, ← map_mul, ← hu, Units.mul_inv, map_one]
    rw [← hu] at h1
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  have hfix : ∀ g, sg p ρ g s = s := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    simp only [← sg_mul]
    exact sum_shift (Nm ρ p m) (fun g => sg p ρ g T)
      (fun g ν hν => by simp only [sg_mul, sg_fix ρ hν hT]) g
  refine ⟨T * ↑u⁻¹, Subring.mul_mem _ hT (hinv _ hsS), ?_⟩
  simp only [map_mul, hinv _ (hfix _)]
  rw [← Finset.sum_mul, ← hs, ← hu, Units.mul_inv]

private noncomputable def Mw (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [CommRing R] [CharP R p]
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (g : G) :
    Matrix (Fin r) (Fin r) (WittVector p R) := (M g).map (zlW p R)

private def Good (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (n : ℕ)
    (W : Matrix (Fin r) (Fin r) (WittVector p R)) : Prop :=
  (∃ m, 0 < m ∧ ∀ i j, W i j ∈ Sm p R m) ∧
    ∀ g, (Mw p R M g * W.map (sg p ρ g)).map (WittVector.truncate n) = W.map (WittVector.truncate n)

omit [IsDomain R] in
private lemma Mw_mul {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (g h : G) :
    Mw p R M (g * h) = Mw p R M g * Mw p R M h := by
  simp only [Mw, map_mul, Matrix.map_mul]

omit [IsDomain R] in
private lemma Mw_one {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) :
    Mw p R M 1 = 1 := by
  simp [Mw]

omit [IsDomain R] in
private lemma good_avg (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    {n m : ℕ} (hm : 0 < m) [Fintype (G ⧸ Nm ρ p m)]
    (hN : ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1)
    (B : Matrix (Fin r) (Fin r) (WittVector p R)) (hB : ∀ i j, B i j ∈ Sm p R m) :
    Good ρ M n (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) ∧
      ∀ i j, (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) i j ∈ Sm p R m := by
  have h1 : ∀ i j, (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) i j ∈ Sm p R m := by
    intro i j
    rw [Matrix.sum_apply]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (zl_mem _ _) (sg_mem ρ _ (hB _ _))
  refine ⟨⟨⟨m, hm, h1⟩, fun g => ?_⟩, h1⟩
  refine avg (sg p ρ) (sg_mul ρ) (Mw p R M) (Mw_mul M) (fun g h => ?_) _ (Nm ρ p m) hN B
    (fun ν hν => ?_) g
  · ext1 i j
    exact map_zl _ _
  · ext1 i j
    exact sg_fix ρ hν (hB i j)

private lemma step (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m)) (n : ℕ)
    (hlev : ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate (n + 1)) = 1)
    (W : Matrix (Fin r) (Fin r) (WittVector p R)) (hW : Good ρ M n W) :
    ∃ W', Good ρ M (n + 1) W' ∧ W'.map (WittVector.truncate n) = W.map (WittVector.truncate n) := by
  obtain ⟨a, ha, hN⟩ := hlev
  obtain ⟨⟨b, hb, hS⟩, hW⟩ := hW
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have := hfin _ hm
  have := Fintype.ofFinite (G ⧸ Nm ρ p (a * b))
  obtain ⟨t, ht, ht1⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (p := p) ρ hm
  have hS' : ∀ i j, W i j ∈ Sm p R (a * b) := by
    intro i j
    have := hS i j
    rw [mem_Sm] at this ⊢
    intro k
    rw [mul_comm]
    exact pow_pow_mul (this k) a
  refine ⟨_, (good_avg ρ M hm (fun ν hν => hN ν fun y hy => hν y (pow_pow_mul hy b)) (t • W)
    (fun i j => Subring.mul_mem _ ht (hS' i j))).1, ?_⟩
  have h1 : ∀ g, (Mw p R M g * (t • W).map (sg p ρ g)).map (WittVector.truncate n)
      = WittVector.truncate n (sg p ρ g t) • W.map (WittVector.truncate n) := by
    intro g
    have : (t • W).map (sg p ρ g) = sg p ρ g t • W.map (sg p ρ g) := by
      ext1 i j; simp
    rw [this, Matrix.mul_smul, ← hW g]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.mapMatrix_apply, map_sum]
  simp only [RingHom.mapMatrix_apply, h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_smul, ← map_sum, ht1, map_one, one_smul]

private lemma base (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m))
    (hlev : ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate 1) = 1) :
    ∃ W, Good ρ M 1 W ∧ IsUnit (W.det.coeff 0) := by
  obtain ⟨m, hm, hN⟩ := hlev
  have := hfin _ hm
  have := Fintype.ofFinite (G ⧸ Nm ρ p m)
  let c : WittVector p R →+* R := WittVector.constantCoeff
  let q0 : G ⧸ Nm ρ p m := ((1 : G) : _)
  obtain ⟨B, hB⟩ := det_domain (chi ρ p m) (chi_inj ρ m) (fun q => (Mw p R M q.out).map c) q0
    ((Mw p R M q0.out⁻¹).map c) (by
      rw [← Matrix.map_mul, ← Mw_mul, mul_inv_cancel, Mw_one]; simp)
  obtain ⟨h1, h2⟩ := good_avg ρ M hm hN (B.map fun a => WittVector.teichmuller p (a : R))
    (fun i j => teich_mem ((mem_Km m _).1 (B i j).2))
  refine ⟨_, h1, unit_of_per hm ((mem_Sm m _).1 ?_ 0) ?_⟩
  · rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => h2 _ _)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← WittVector.constantCoeff_apply, RingHom.map_det, map_sum]
      have hs : (∑ q : G ⧸ Nm ρ p m,
          c.mapMatrix (Mw p R M q.out *
            (B.map fun a => WittVector.teichmuller p (a : R)).map (sg p ρ q.out))) =
          ∑ q, (Mw p R M q.out).map c * B.map (chi ρ p m q) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [RingHom.mapMatrix_apply, Matrix.map_mul]
        congr 1
      rw [hs]
      exact hB

private lemma core (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m))
    (hlev : ∀ n, ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ (g : G) (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        Mw p R M g * W.map (WittVector.map f) = W := by
  obtain ⟨W0, hW0, hd⟩ := base ρ M hfin (hlev 1)
  choose F hF1 hF2 using fun n => step ρ M hfin (n + 1) (hlev _)
  let s : ∀ n : ℕ, {W // Good ρ M (n + 1) W} := fun n =>
    Nat.rec ⟨W0, hW0⟩ (fun n w => ⟨F n w.1 w.2, hF1 n w.1 w.2⟩) n
  have hs0 : (s 0).1 = W0 := rfl
  have hs : ∀ n i j k, k < n + 1 → ((s (n + 1)).1 i j).coeff k = ((s n).1 i j).coeff k := by
    intro n i j
    rw [← trunc_iff]
    exact congrFun (congrFun (hF2 n (s n).1 (s n).2) i) j
  have hs' : ∀ i j k n, k ≤ n → ((s n).1 i j).coeff k = ((s k).1 i j).coeff k := by
    intro i j k n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hs n i j k (by omega), ih]
  let W : Matrix (Fin r) (Fin r) (WittVector p R) :=
    fun i j => WittVector.mk p fun k => ((s k).1 i j).coeff k
  have hW : ∀ i j k, (W i j).coeff k = ((s k).1 i j).coeff k := fun _ _ _ => rfl
  refine ⟨W, unit_of_coeff ?_, fun g f hf => ?_⟩
  · rw [← WittVector.constantCoeff_apply, RingHom.map_det] at hd ⊢
    convert hd using 2
    ext i j
    simp [hW, hs0]
  · have key : ∀ n, (Mw p R M g * W.map (WittVector.map f)).map (WittVector.truncate (n + 1))
        = W.map (WittVector.truncate (n + 1)) := by
      intro n
      obtain ⟨⟨m, hm, hS⟩, hG⟩ := (s n).2
      have e1 : W.map (WittVector.truncate (n + 1)) = (s n).1.map (WittVector.truncate (n + 1)) := by
        ext1 i j
        simp only [Matrix.map_apply]
        rw [trunc_iff]
        intro k hk
        rw [hW, hs' i j k n (by omega)]
      have e2 : (W.map (WittVector.map f)).map (WittVector.truncate (n + 1))
          = ((s n).1.map (sg p ρ g)).map (WittVector.truncate (n + 1)) := by
        ext1 i j
        simp only [Matrix.map_apply]
        rw [trunc_iff]
        intro k hk
        rw [WittVector.map_coeff, sg_coeff, hW, ← hs' i j k n (by omega)]
        exact hf m hm _ ((mem_Sm m _).1 (hS i j) k)
      rw [e1, ← hG g, Matrix.map_mul, Matrix.map_mul, e2]
    ext i j k
    exact (trunc_iff (k + 1) _ _).1 (congrFun (congrFun (key k) i) j) k (Nat.lt_succ_self k)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [CharP R p] [CompactSpace G] in
private lemma Nm_open (ρ : G →* R ≃+* R)
    (h : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ρ g y = y)
    {m : ℕ} (hm : 0 < m) : IsOpen (Nm ρ p m : Set G) := by
  classical
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hfin : {y : R | y ^ p ^ m = y}.Finite := by
    have hne : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R) ≠ 0 :=
      by
      intro h0
      have h2 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h2
      omega
    refine (Polynomial.roots (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R)).toFinset.finite_toSet.subset ?_
    intro y hy
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simpa [sub_eq_zero] using hy
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact (Filter.eventually_all_finite hfin).2 fun y hy => h y m hm hy

private lemma level (ρ : G →* R ≃+* R)
    (h : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hc : Continuous M)
    (hM : ∀ g : G, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) (n : ℕ) :
    ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1 := by
  let U : Set G := ⋂ i, ⋂ j, {g | ‖M g i j - (1 : Matrix (Fin r) (Fin r) ℤ_[p]) i j‖
    < (p : ℝ) ^ (-(n : ℤ) + 1)}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt (((hc.matrix_elem i j).sub continuous_const).norm) continuous_const
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  obtain ⟨m, hm⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : ℕ+ => (Nm ρ p m : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (Nm_open ρ h m.2))
    (by
      rw [Set.disjoint_left]
      intro g hg hg'
      apply hg
      rw [Set.mem_iInter] at hg'
      have := hM g fun m hm => hg' ⟨m, hm⟩
      simp only [U, Set.mem_iInter, Set.mem_ofPred_eq, this, sub_self, norm_zero]
      intro i j
      positivity)
    (fun a b => ⟨a * b, fun g hg y hy => hg y (pow_pow_mul hy b), fun g hg y hy => hg y (by
      rw [mul_comm]; exact pow_pow_mul hy a)⟩)
  refine ⟨m, m.2, fun ν hν => ?_⟩
  have hν' : ν ∈ U := by
    by_contra hn
    exact Set.disjoint_left.1 hm hn hν
  simp only [U, Set.mem_iInter, Set.mem_ofPred_eq] at hν'
  ext1 i j
  have := hν' i j
  rw [← PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton'] at this
  obtain ⟨c, hc⟩ := this
  have e : M ν i j = (1 : Matrix (Fin r) (Fin r) ℤ_[p]) i j + c * (p : ℤ_[p]) ^ n := by
    rw [hc]; ring
  have z : WittVector.truncate n (zlW p R c * (p : WittVector p R) ^ n) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro k hk
    exact WittVector.mul_pow_charP_coeff_zero _ hk
  simp only [Mw, Matrix.map_apply]
  rw [e, map_add (f := _), map_mul, map_pow, map_natCast, map_add (f := _), z, add_zero]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

end

private theorem exists_trivialization {p : ℕ} [Fact p.Prime] {G R : Type} [Group G] [CommRing R]
    (ρ : G →* R ≃+* R) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in nhds (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hker : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W := by
  obtain ⟨W, hdet, hW⟩ := core ρ M
    (fun m hm => Subgroup.quotient_finite_of_isOpen _ (Nm_open ρ hopen hm))
    (level ρ hopen M hM hker)
  exact ⟨W, hdet, fun g => hW g (ρ g).toRingHom (fun _ _ _ _ => rfl)⟩

end UpperTheory.Reformulated.B.RestrictAutomorphism

theorem UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  (∀ (g : G),
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.RestrictAutomorphism.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map ((ρ : G → R ≃+* R) g).toRingHom) : WittVector p R → WittVector p R) =
                        W) ∧
                    ∀ (i j : Fin r) (n : ℕ), ∃ (m : ℕ), (0 : ℕ) < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n := by
  intro p hp G _ R _ ρ _ _ _ _ _ hopen r M hM hker
  have : CharP (algPart p R) p := inferInstance
  obtain ⟨V, hV, hVeq⟩ := exists_trivialization (p := p) (restrictHom p ρ)
    (fun y m hm hy => (hopen y m hm (by simpa using congrArg Subtype.val hy)).mono
      fun g hg => Subtype.ext hg)
    M hM
    (fun g hg => hker g fun m hm y hy =>
      congrArg Subtype.val (hg m hm ⟨y, m, hm, hy⟩ (Subtype.ext (by simpa using hy))))
  let ι : WittVector p (algPart p R) →+* WittVector p R := WittVector.map (algPart p R).subtype
  refine ⟨V.map ι, ?_, fun g => ?_, fun i j n => ?_⟩
  · have h := hV.map ι
    rwa [RingHom.map_det] at h
  · have h := congrArg (fun A => A.map ι) (hVeq g)
    have h1 : (M g).map (zlW p R) =
        ((M g).map (zlW p (algPart p R))).map ι := by
      rw [hom_unique (zlW p R) (ι.comp (zlW p (algPart p R))), RingHom.coe_comp, Matrix.map_map]
    have h2 : (V.map ι).map (WittVector.map (ρ g).toRingHom) =
        (V.map (WittVector.map (restrictHom p ρ g).toRingHom)).map ι := by
      ext i j n
      simp only [Matrix.map_apply, ι, WittVector.map_coeff]
      rfl
    rw [h1, h2, ← Matrix.map_mul]
    exact h
  · simp only [Matrix.map_apply, ι, WittVector.map_coeff]
    exact ((V i j).coeff n).2
