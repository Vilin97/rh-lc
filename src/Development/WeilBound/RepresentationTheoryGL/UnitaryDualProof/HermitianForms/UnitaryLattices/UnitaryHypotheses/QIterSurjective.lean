module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.BlkAtApply
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelDerivativeZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def qIter (ψ : AddChar k Circle) {n : ℕ} : (j : ℕ) → (τ : MRep k (n + j)) → τ.V →ₗ[ℂ] (iterPhi k ψ j τ).V
  | 0, _ => LinearMap.id
  | j + 1, τ => (qIter ψ j (MRep.phiM k ψ τ)).comp (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ


variable (k) in
def emb (n : ℕ) : (j : ℕ) → Mir k n →* Mir k (n + j)
  | 0 => MonoidHom.id _
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (emb n j)

theorem qIter_surjective (ψ : AddChar k Circle) {n : ℕ} :
    ∀ (j : ℕ) (τ : MRep k (n + j)), Function.Surjective (qIter k ψ j τ)
  | 0, _ => Function.surjective_id
  | j + 1, τ => (qIter_surjective ψ j (MRep.phiM k ψ τ)).comp (Submodule.mkQ_surjective _)

theorem qIter_equiv (ψ : AddChar k Circle) {n : ℕ} :
    ∀ (j : ℕ) (τ : MRep k (n + j)) (p : Mir k n) (v : τ.V),
      qIter k ψ j τ (τ.ρ (emb k n j p) v) = (iterPhi k ψ j τ).ρ p (qIter k ψ j τ v)
  | 0, _, _, _ => rfl
  | j + 1, τ, p, v => by
    have ih := qIter_equiv ψ j (MRep.phiM k ψ τ) p
      ((twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ v)
    exact ih

theorem ker_qIter (ψ : AddChar k Circle) {n : ℕ} :
    ∀ (j : ℕ) (τ : MRep k (n + j)),
      LinearMap.ker ((twKer (iterPhi k ψ j τ).ρ (MirUin k n) 1).mkQ ∘ₗ qIter k ψ j τ) =
        twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)
  | 0, τ => by
    exact (Submodule.ker_mkQ _).trans (GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ)
  | j + 1, τ => by
    let s := (levi k (n + j + 1)).comp (Mir k (n + j)).subtype
    let N₁ := MirUin k (n + j + 1)
    let N₂ := derUnipM k (n + j) n
    let N := derUnipM k (n + j + 1) n
    let θ₁ := mirChar k ψ (n + j)
    let θ₂ := derCharM k ψ (n + j) n
    let θ := derCharM k ψ (n + j + 1) n
    let K := twKer τ.ρ N₁ θ₁
    let L := twKer τ.ρ N θ
    let T := twKer (MRep.phiM k ψ τ).ρ N₂ θ₂
    have h₁ (u : N₁) : ∃ h : (u : Mir k (n + j + 1)) ∈ N, θ ⟨u, h⟩ = θ₁ u :=
      GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ (Nat.le_add_right n j) u
    have h₂ (a : N₂) : ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a :=
      GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ (Nat.le_add_right n j) a
    have hle : K ≤ L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      obtain ⟨h, hθ⟩ := h₁ u
      exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
    have e : T = L.map K.mkQ := by
      refine le_antisymm (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨a, x, rfl⟩
        induction x using Submodule.Quotient.induction_on with
        | H v =>
          obtain ⟨h, hθ⟩ := h₂ a
          refine ⟨τ.ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v,
            Submodule.subset_span ⟨⟨s a, h⟩, v, rfl⟩, ?_⟩
          rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
          rfl
      · refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)
        rintro _ ⟨u, v, rfl⟩
        obtain ⟨u₁, a, hu⟩ := GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp
          (Nat.le_add_right n j) u
        change (u : Mir k (n + j + 1)) = u₁ * s a at hu
        obtain ⟨hu₁, hθ₁⟩ := h₁ u₁
        obtain ⟨ha, hθ₂⟩ := h₂ a
        have hθ : θ u = θ₁ u₁ * θ₂ a := by
          have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
          rw [this, map_mul, hθ₁, hθ₂]
        have hdec : τ.ρ (u : Mir k (n + j + 1)) v - ((θ u : ℂˣ) : ℂ) • v =
            (τ.ρ u₁ (τ.ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • τ.ρ (s a) v) +
              ((θ₁ u₁ : ℂˣ) : ℂ) • (τ.ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
          rw [hθ, hu, map_mul, Module.End.mul_apply, Units.val_mul, smul_sub, mul_smul]
          abel
        have hz : τ.ρ u₁ (τ.ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • τ.ρ (s a) v ∈ K :=
          Submodule.subset_span ⟨u₁, _, rfl⟩
        show K.mkQ _ ∈ T
        rw [hdec, map_add (f := K.mkQ), Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
    have ih := ker_qIter ψ j (MRep.phiM k ψ τ)
    show LinearMap.ker (((twKer (iterPhi k ψ j (MRep.phiM k ψ τ)).ρ (MirUin k n) 1).mkQ ∘ₗ
      qIter k ψ j (MRep.phiM k ψ τ)) ∘ₗ K.mkQ) = L
    refine (LinearMap.ker_comp _ _).trans ?_
    rw [ih]
    change T.comap K.mkQ = L
    rw [e]
    exact (Submodule.comap_map_mkQ _ _).trans (sup_eq_right.2 hle)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem glEmbMat_apply' (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin (n + 1)) :
    glEmbMat k n A a b =
      if ha : (a : ℕ) < n then (if hb : (b : ℕ) < n then A ⟨a, ha⟩ ⟨b, hb⟩ else 0)
      else (if a = b then 1 else 0) := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b => simp [glEmbMat, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b => simp [glEmbMat]

theorem emb_val (n : ℕ) (p : Mir k n) :
    ∀ (j : ℕ) (a b : Fin (n + j + 1)),
      (((emb k n j p : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b =
        if ha : (a : ℕ) < n + 1 then
          (if hb : (b : ℕ) < n + 1 then ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ⟨a, ha⟩ ⟨b, hb⟩
            else 0)
        else (if a = b then 1 else 0)
  | 0, a, b => by
    rw [dif_pos a.isLt, dif_pos b.isLt]
    rfl
  | j + 1, a, b => by
    have ih := emb_val n p j
    show glEmbMat k (n + j + 1) (((emb k n j p : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
      Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b = _
    rw [glEmbMat_apply']
    by_cases ha : (a : ℕ) < n + j + 1
    · by_cases hb : (b : ℕ) < n + j + 1
      · rw [dif_pos ha, dif_pos hb, ih]
        by_cases ha' : (a : ℕ) < n + 1
        · rw [dif_pos ha', dif_pos ha']
        · rw [dif_neg ha', dif_neg ha']
          simp only [Fin.ext_iff]
      · rw [dif_pos ha, dif_neg hb]
        have hb' : ¬ (b : ℕ) < n + 1 := by omega
        by_cases ha' : (a : ℕ) < n + 1
        · rw [dif_pos ha', dif_neg hb']
        · rw [dif_neg ha', if_neg]
          intro h
          rw [h] at ha
          exact hb ha
    · rw [dif_neg ha]
      have ha' : ¬ (a : ℕ) < n + 1 := by omega
      rw [dif_neg ha']

theorem emb_levi (n j : ℕ) (g : GL (Fin n) k) :
    ((emb k n j (levi k n g) : Mir k (n + j)) : GL (Fin (n + j + 1)) k) = blkAt k n (n + j + 1) (by omega) g := by
  ext a b
  rw [emb_val, blkAt_apply]
  have hl : ∀ (a' b' : Fin (n + 1)), (((levi k n g : Mir k n) : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) a' b' = glEmbMat k n (g : Matrix (Fin n) (Fin n) k) a' b' := fun _ _ => rfl
  by_cases ha : (a : ℕ) < n
  · have ha' : (a : ℕ) < n + 1 := by omega
    rw [dif_pos ha', dif_pos ha]
    by_cases hb : (b : ℕ) < n
    · have hb' : (b : ℕ) < n + 1 := by omega
      rw [dif_pos hb', dif_pos hb, hl, glEmbMat_apply']
      simp only [ha, hb, dif_pos]
    · rw [dif_neg hb]
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true]
      · rw [dif_neg hb']
  · rw [dif_neg ha]
    by_cases ha' : (a : ℕ) < n + 1
    · rw [dif_pos ha']
      by_cases hb' : (b : ℕ) < n + 1
      · rw [dif_pos hb', hl, glEmbMat_apply']
        simp only [ha, dif_neg, not_false_eq_true]
        simp only [Fin.ext_iff]
      · rw [dif_neg hb']
        split_ifs with h <;> first | rfl | (simp only [Fin.ext_iff] at h; omega)
    · rw [dif_neg ha']

theorem derDict (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) :
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ g v, q (π (blkAt k n (n + j + 1) (by omega) g) v) = deriv k ψ j π g (q v) := by
  refine ⟨(twKer (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1).mkQ ∘ₗ qIter k ψ j (resM k π), ?_, ?_, ?_⟩
  · exact (Submodule.mkQ_surjective _).comp (qIter_surjective ψ j _)
  · exact (ker_qIter ψ j (resM k π)).trans (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + j) n V π)
  · intro g v
    rw [← emb_levi n j g]
    show (twKer (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1).mkQ
        (qIter k ψ j (resM k π) ((resM k π).ρ (emb k n j (levi k n g)) v)) =
      (twKer (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1).mkQ
        ((iterPhi k ψ j (resM k π)).ρ (levi k n g) (qIter k ψ j (resM k π) v))
    exact congrArg _ (qIter_equiv ψ j (resM k π) (levi k n g) v)

end PositivityTheory.RgUd.Form.U.Asm
