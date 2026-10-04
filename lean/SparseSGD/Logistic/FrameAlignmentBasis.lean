import SparseSGD.Logistic.MarkovReduction
namespace SparseSGD.Logistic
noncomputable section
open scoped RealInnerProductSpace
set_option maxHeartbeats 1800000

/-- Every full logistic state has an actual orthogonal frame with the signal
first and at most two active bulk coordinates. Degenerate state spans are
handled by their actual dimension. -/
theorem exists_active_logistic_frame {d : ℕ} (mu theta m : Vec d) (hr : 0 < r mu) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 3 ∧ q ≤ d ∧
      ∃ O : Vec d ≃ₗᵢ[ℝ] Vec d, ∃ i0 : Fin d, i0.val=0 ∧
        O mu=EuclideanSpace.single i0 (r mu) ∧
        (∀ j : Fin d, q ≤ j.val → (O theta) j=0) ∧
        (∀ j : Fin d, q ≤ j.val → (O m) j=0) := by
  classical
  let v : Fin 3 → Vec d := ![mu,theta,m]
  let S := Submodule.span ℝ (Set.range v)
  have hmu : mu ∈ S := Submodule.subset_span ⟨0,by simp [v]⟩
  have htheta : theta ∈ S := Submodule.subset_span ⟨1,by simp [v]⟩
  have hm : m ∈ S := Submodule.subset_span ⟨2,by simp [v]⟩
  let q := Module.finrank ℝ S
  have hq3 : q ≤ 3 := by
    have hc := finrank_span_le_card (R:=ℝ) (Set.range v)
    have hc2 := Fintype.card_range_le v
    rw [Set.toFinset_card] at hc
    dsimp [q,S]
    exact hc.trans (by simpa using hc2)
  have hqd : q ≤ d := by
    exact S.finrank_le.trans (by simp [Vec,SparseSGD.Probability.LeastSquares.Vec,finrank_euclideanSpace])
  have hmunz : mu ≠ 0 := by intro hz; simp [r,hz] at hr
  let muS : S := ⟨mu,hmu⟩
  have hmunzS : muS ≠ 0 := by intro hz; apply hmunz; exact congrArg Subtype.val hz
  have : Nontrivial S := ⟨⟨muS,0,hmunzS⟩⟩
  have hqpos : 0 < q := Module.finrank_pos_iff.mpr inferInstance
  let i0q : Fin q := ⟨0,hqpos⟩
  let u : S := (r mu)⁻¹ • muS
  have hu : ‖u‖=1 := by
    rw [show u = (r mu)⁻¹ • muS from rfl, norm_smul, Real.norm_eq_abs]
    change |(r mu)⁻¹| * ‖mu‖ = 1
    rw [abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hON : Orthonormal ℝ (({i0q}:Set (Fin q)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.val=i0q := Set.mem_singleton_iff.mp i.property
    have hj : j.val=i0q := Set.mem_singleton_iff.mp j.property
    have hij : i=j := Subtype.ext (hi.trans hj.symm)
    subst j
    simp only [Set.domRestrict_apply, ite_true]
    change inner ℝ u u = 1
    rw [real_inner_self_eq_norm_sq,hu]
    norm_num
  have hcard : Module.finrank ℝ S = Fintype.card (Fin q) := by simp [q]
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (ι:=Fin q) (v:=fun _ : Fin q => u) (s:={i0q}) hcard hON
  have hb0 : b i0q=u := hb i0q (Set.mem_singleton _)
  let target := fun i : Fin q => (EuclideanSpace.single (Fin.castLE hqd i) (1:ℝ) : Vec d)
  have htarget : Orthonormal ℝ target := (EuclideanSpace.orthonormal_single (𝕜:=ℝ) (ι:=Fin d)).comp
    (Fin.castLE hqd) (Fin.castLE_injective hqd)
  let L := b.toBasis.constr ℝ target
  have hL : Orthonormal ℝ (L ∘ b.toBasis) := by
    have hfun : (L ∘ b.toBasis) = target := by
      funext i
      exact b.toBasis.constr_basis ℝ target i
    rw [hfun]
    exact htarget
  let I : S →ₗᵢ[ℝ] Vec d := L.isometryOfOrthonormal (v:=b.toBasis) b.orthonormal hL
  let O := I.extend.toLinearIsometryEquiv rfl
  have hOS (x : S) : O x=I x := by
    change I.extend.toLinearIsometryEquiv rfl x=I x
    rw [LinearIsometry.toLinearIsometryEquiv_apply]
    exact I.extend_apply x
  have hIb (i : Fin q) : I (b i)=target i := by
    change L (b i)=target i
    exact b.toBasis.constr_basis ℝ target i
  have hunit : muS=(r mu) • u := by
    dsimp [u]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hOm : O mu=(r mu) • target i0q := by
    change O muS=_
    rw [hOS,hunit,map_smul,← hb0,hIb]
  have hsupport (x : S) (j : Fin d) (hj : q ≤ j.val) : (O x) j=0 := by
    rw [hOS]
    change (L x) j=0
    rw [Module.Basis.constr_apply_fintype]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hneq : j ≠ Fin.castLE hqd i := by intro heq; have he := congrArg Fin.val heq; simp at he; omega
    simp [target,hneq]
  refine ⟨q,hqpos,hq3,hqd,O,Fin.castLE hqd i0q,rfl,?_,?_,?_⟩
  · rw [hOm]
    ext j
    simp [target,PiLp.single_apply,PiLp.smul_apply]
  · exact fun j hj => hsupport ⟨theta,htheta⟩ j hj
  · exact fun j hj => hsupport ⟨m,hm⟩ j hj

/-- The constructed active span contains the signal and at most two bulk axes.
The remaining dimension is a genuine Gaussian complement, possibly zero. -/
theorem exists_two_bulk_logistic_frame {d : ℕ} (mu theta momentum : Vec d) (hr : 0<r mu) :
    ∃ k rest : ℕ, k≤2 ∧ d=(k+1)+rest ∧
      ∃ O : Vec d ≃ₗᵢ[ℝ] Vec d, ∃ i0 : Fin d, i0.val=0 ∧
        O mu=EuclideanSpace.single i0 (r mu) ∧
        (∀ j : Fin d, k+1≤j.val → (O theta) j=0) ∧
        (∀ j : Fin d, k+1≤j.val → (O momentum) j=0) := by
  obtain ⟨q,hqpos,hq3,hqd,O,i0,hi0,hmu,htheta,hmomentum⟩ := exists_active_logistic_frame mu theta momentum hr
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
  refine ⟨k,d-q,by omega,?_,O,i0,hi0,hmu,?_,?_⟩
  · omega
  · intro j hj
    exact htheta j (by omega)
  · intro j hj
    exact hmomentum j (by omega)
end
end SparseSGD.Logistic
