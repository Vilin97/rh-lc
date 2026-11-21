module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Grow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem leftInv {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
  exact this

theorem exists_kill {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧ ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  obtain ⟨hA, hS, _, hCT⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  have hct := (hCT φ hφ r hr0 hrN).1
  have hfin := finTr_holds E N φ hφ r hr0 hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
    rw [hA, hA, hA]; exact JSqIntGlue.aR_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp hnice.cont r ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [hA] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    exact ⟨c, ⟨_, hct, F, hF, hF0, hFe⟩, rfl⟩

theorem bnd_of' {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) : An.Bnd φ.1 κ := by
  obtain ⟨_, hS, _, _⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  obtain ⟨M, hM⟩ := initBnd_holds E N φ hφ hcen'
  have hctstep : An.CtStepGlue := by
    open PositivityTheory.Rg.Rs.An PositivityTheory.Rg.Rs.ctstepglue GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm in
      intro hrec K _ _ n φ m r p κ hr hrn hφ hB hp hK hroot ω hω hωB t₀ Q hQ
      obtain ⟨C₁, hC₁⟩ := bnd_ctn (r := r) hB ω hω hωB t₀ Q hQ
      obtain ⟨C₂, hC₂0, hC₂⟩ := hrec p κ hp hroot
      set d := p.natDegree with hd
      set E : ℝ := Real.exp (|m r| * (|t₀| + 1 + d)) with hE
      refine ⟨C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)), ?_⟩
      intro b hb x hx q hq
      set S : ℝ := ∑ r' ∈ (Finset.range n).erase r, m r' * sr x r' with hS
      have hrmem : r ∈ Finset.range n := Finset.mem_range.2 hrn
      have hsum : ∀ (f : ℕ → ℝ) (y : Fin n → ℝ), (∀ r' ≠ r, f r' = m r') → (∀ r' ≠ r, sr y r' = sr x r') →
          ∑ r' ∈ Finset.range n, f r' * sr y r' = f r * sr y r + S := by
        intro f y hf hy
        rw [← Finset.add_sum_erase _ _ hrmem, hS]
        congr 1
        refine Finset.sum_congr rfl fun r' h' => ?_
        rw [hf r' (Finset.ne_of_mem_erase h'), hy r' (Finset.ne_of_mem_erase h')]
      have h0 : 0 ≤ sr x r + t₀ := by linarith [hx r]
      set i : ℕ := ⌊sr x r + t₀⌋₊ with hi
      have hi1 : (i : ℝ) ≤ sr x r + t₀ := Nat.floor_le h0
      have hi2 : sr x r + t₀ < i + 1 := Nat.lt_floor_add_one _
      set x' : Fin n → ℝ := shift r x (-(i : ℝ)) with hx'
      set g₀ : AdelicGLn.AdelicGL K n := b * tor K x' * q with hg₀
      set u : ℕ → ℂ := fun k => ctn r φ (aR K n r k * g₀) with hu
      have hrecu : ∀ k, ∑ j ∈ Finset.range (d + 1), p.coeff j * u (k + j) = 0 := by
        intro k
        have := hK (aR K n r k * g₀)
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hu, ← mul_assoc, aR_mul]
        congr 4
        push_cast; ring
    
      have hmove : ∀ (t : ℝ) (h : AdelicGLn.AdelicGL K n), ctn r φ (aR K n r t * (b * h)) = ctn r φ (b * (aR K n r t * h)) := by
        intro t h
        obtain ⟨X, hX⟩ := borel_aR (r := r) (hωB hb) t
        have : aR K n r t * b = unipGL (-X) * (b * aR K n r t) := by
          rw [hX, ← mul_assoc, ← unipGL_add, neg_add_cancel, unipGL_zero, one_mul]
        rw [← mul_assoc, this, mul_assoc, ctn_unipGL_mul hφ.left, ← mul_assoc]
      set M : ℝ := max C₁ 0 * E * Real.exp S with hM
      have hM0 : 0 ≤ M := by positivity
      have hinit : ∀ j < d, ‖u j‖ ≤ M := by
        intro j hj
        have e1 : u j = ctn r φ (b * tor K (shift r x ((j : ℝ) - i)) * q) := by
          simp only [hu, hg₀, mul_assoc]
          rw [hmove, ← mul_assoc (aR K n r j), ← tor_shift, hx',
            show shift r (shift r x (-(i : ℝ))) (j : ℝ) = shift r x ((j : ℝ) - i) from by
              funext l; simp only [shift]; split_ifs <;> ring]
        have hsr : ∀ r', sr (shift r x ((j : ℝ) - i)) r' = sr x r' + if r' = r then (j : ℝ) - i else 0 :=
          sr_shift hr hrn x _
        have hx2 : ∀ r', -t₀ ≤ sr (shift r x ((j : ℝ) - i)) r' := by
          intro r'
          rw [hsr]
          split_ifs with h
          · subst h; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
          · simpa using hx r'
        have hb1 := hC₁ b hb _ hx2 q hq
        rw [e1]
        refine hb1.trans ?_
        rw [hsum m _ (fun _ _ => rfl) (fun r' h => by rw [hsr, if_neg h, add_zero]), hsr, if_pos rfl,
          Real.exp_add, hM, ← mul_assoc]
        have hjd : (j : ℝ) ≤ d := by exact_mod_cast hj.le
        have hv : |sr x r + ((j : ℝ) - i)| ≤ |t₀| + 1 + d := by
          rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
        have hexp : Real.exp (m r * (sr x r + ((j : ℝ) - i))) ≤ E := by
          rw [hE]; apply Real.exp_le_exp.2
          calc m r * (sr x r + ((j : ℝ) - i)) ≤ |m r * (sr x r + ((j : ℝ) - i))| := le_abs_self _
            _ = |m r| * |sr x r + ((j : ℝ) - i)| := abs_mul _ _
            _ ≤ |m r| * (|t₀| + 1 + d) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
        have hC : C₁ ≤ max C₁ 0 := le_max_left _ _
        gcongr
      have hmain := hC₂ u M hrecu hinit hM0 i
      have heq : ctn r φ (b * tor K x * q) = u i := by
        have : x = shift r x' (i : ℝ) := by
          funext l; simp only [hx', shift]; split_ifs <;> ring
        simp only [hu, hg₀]
        conv_lhs => rw [this, tor_shift]
        rw [mul_assoc b (tor K x') q, hmove]
        simp only [mul_assoc]
      rw [heq]
      refine hmain.trans ?_
      rw [hsum (Function.update m r κ) x (fun r' h => Function.update_of_ne h _ _) (fun _ _ => rfl),
        Function.update_self, Real.exp_add, hM]
      have hk : Real.exp (κ * i) ≤ Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1)) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.2
        have : |(i : ℝ) - sr x r| ≤ |t₀| + 1 := by
          rw [abs_le]; constructor <;> cases abs_cases t₀ <;> linarith
        have := mul_le_mul_of_nonneg_left this (abs_nonneg κ)
        have h2 : κ * ((i : ℝ) - sr x r) ≤ |κ| * |(i : ℝ) - sr x r| := by
          rw [← abs_mul]; exact le_abs_self _
        nlinarith
      have hE0 : 0 ≤ max C₁ 0 * E := by positivity
      calc C₂ * Real.exp (κ * i) * (max C₁ 0 * E * Real.exp S)
          ≤ C₂ * (Real.exp (κ * sr x r) * Real.exp (|κ| * (|t₀| + 1))) * (max C₁ 0 * E * Real.exp S) := by
            gcongr
        _ = C₂ * (max C₁ 0 * E) * Real.exp (|κ| * (|t₀| + 1)) * (Real.exp (κ * sr x r) * Real.exp S) := by ring
  exact GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (hctstep GlobalTheory.CompanionTheory.LinRec.recBound) E N φ.1 M κ hnice hM hκ

theorem bnd_of {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re < κ r) : An.Bnd φ.1 κ := by
  refine bnd_of' hφ hcen κ fun r hr0 hrN => ?_
  obtain ⟨p, hp, hk, hroots⟩ := exists_kill hφ hcen hr0 hrN
  refine ⟨p, hp, hk, fun z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hroots z hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.2 (hκ r hr0 hrN c hc)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_le_rho {r : ℕ} {c : ℂ} (h : pE E N r c ≤ 0) : c.re ≤ An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_le_iff₀ hd).1 h2
  unfold An.rho
  calc c.re ≤ (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_lt_rho {r : ℕ} {c : ℂ} (h : pE E N r c < 0) : c.re < An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_lt_iff₀ hd).1 h2
  unfold An.rho
  calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

end Grow

open Grow in
theorem growPHolds : GrowPHolds := by
  intro E _ _ _ N χ hχ hcen hnp
  refine ⟨ContAut.continuous_of_isOpen_stab E N χ hχ.level, leftInv hχ hcen, fun ε hε => ?_⟩
  exact bnd_of hχ hcen _ fun r hr0 hrN c hc => by
    have := re_le_rho (hnp r hr0 hrN c hc)
    linarith

open Grow in
theorem growQHolds : GrowQHolds := by
  intro E _ _ _ N u hu hsq
  have hcen := hsq.1
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r u.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    obtain ⟨p, hp, hpk, hroots⟩ := exists_kill hu hcen hr0 hrN
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, hc, rfl⟩ := hroots z hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.2 (re_lt_rho (expNeg_holds E N u hu hsq r hr0 hrN c hc))
    obtain ⟨κ, hκ, hκz⟩ := JSqIntGlue.exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, hpk, fun z hz => hκz z ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact hz
  choose κ hκ using hk
  exact ⟨ContAut.continuous_of_isOpen_stab E N u hu.level, leftInv hu hcen, κ, fun r h1 h2 => (hκ r h1 h2).1,
    bnd_of' hu hcen κ fun r h1 h2 => (hκ r h1 h2).2⟩

theorem intBnd : IntBnd := by
  intro E _ _ _ N H hc h0 hl m hm hB
  obtain ⟨_, hS, hL, _⟩ := dict_holds E N
  set φ : GA E N → ℂ := fun g => ((Real.sqrt (H g) : ℝ) : ℂ) with hφ
  have hφc : Continuous φ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hc)
  have hφB : An.Bnd φ (fun r => m r / 2) := by
    intro ω hω hωB t₀ Q hQ
    obtain ⟨C, hC⟩ := hB ω hω hωB t₀ Q hQ
    refine ⟨Real.sqrt (max C 0), fun b hb x hx q hq => ?_⟩
    have h1 := hC b hb x hx q hq
    rw [Complex.norm_real, Real.norm_of_nonneg (h0 _)] at h1
    set S := ∑ r ∈ Finset.range N, m r * An.sr x r with hSdef
    have e2 : ∑ r ∈ Finset.range N, m r / 2 * An.sr x r = S / 2 := by
      rw [hSdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    have e : Real.exp (∑ r ∈ Finset.range N, m r / 2 * An.sr x r) = Real.sqrt (Real.exp S) := by
      rw [e2]
      conv_rhs => rw [show S = S / 2 + S / 2 by ring]
      rw [Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have h2 : H (b * An.tor E x * q) ≤ max C 0 * Real.exp S :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖φ (b * An.tor E x * q)‖ = Real.sqrt (H (b * An.tor E x * q)) := by
          rw [hφ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max C 0 * Real.exp S) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (max C 0) * Real.sqrt (Real.exp S) := Real.sqrt_mul (le_max_right _ _) _
      _ = _ := by rw [e]
  have hκ : ∀ r, 0 < r → r < N → m r / 2 < An.rho E N r := fun r h1 h2 => by
    have := hm r h1 h2
    linarith
  have hslab := GlobalTheory.CompanionTheory.SlabGlue.slabGlue boxvol_holds E N Measure.haar φ (fun r => m r / 2) hφc hφB hκ
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hle := JSqIntGlue.setLIntegral_le_of_cover hfd (S := An.slab ω (max 0 (-Real.log t)))
    (fun g => by
      obtain ⟨γ, hγ, h⟩ := JSqIntGlue.exists_mem_slab hS hL ht hsieg g
      exact ⟨⟨γ, hγ⟩, h⟩) (fun g => ENNReal.ofReal (H g)) (fun γ g => by
      show ENNReal.ofReal (H (γ.1 * g)) = ENNReal.ofReal (H g)
      rw [hl γ.1 γ.2 g])
  have e : ∀ g, ‖φ g‖ₑ ^ 2 = ENNReal.ofReal (H g) := fun g => by
    show ‖((Real.sqrt (H g) : ℝ) : ℂ)‖ₑ ^ 2 = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (h0 g)]
  simp only [e] at hslab
  exact hle.trans_lt (hslab ω hω hωB _)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
