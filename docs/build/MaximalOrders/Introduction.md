
<a id='Introduction-1'></a>

# Introduction


In Hecke, maximal orders (aka ring of integers), due to their special properties normal orders don't share, come with their own type `NfMaximalOrder`.  While the elements have type `NfOrderElem`, the ideals and fractional ideals have types `NfMaximalOrderIdeal` and `NfMaximalOrderFracIdeal` respectively.


While theoretically a number field contains a unique maximal order (the set of all integral elements), for technical reasons in Hecke a number field admits multiple maximal orders, which are uniquely determined by the number field and a chosen integral basis.


Let $K$ be a number field of degree $d$ with primitive element $\alpha$ and $\mathcal O$ a maximal order $K$ with $\mathbf{Z}$-basis $(\omega_1,\dotsc,\omega_d)$. The *basis matrix* of $\mathcal O$ is the unique matrix $M_{\mathcal O} \in \operatorname{Mat}_{d \times d}(\mathbf{Q})$ such that \begin{align} \begin{pmatrix} \omega_1 \\ \omega_2 \\ \vdots \\ \omega_d \end{pmatrix} = M_{\mathcal O} \begin{pmatrix} 1 \\ \alpha \\ \vdots \\ \alpha^{d - 1} \end{pmatrix}. \end{align} If $\beta$ is an element of $\mathcal O$, we call the unique integers $(x_1,\dotsc,x_d) \in \mathbf Z^d$ with \begin{align} \beta = \sum_{i=1}^d x_i \omega_i \end{align} the *coefficients* of $\beta$ with respect to $\mathcal O$ or just the *coefficient vector*.


For an ideal $I$ of $\mathcal O$, a *basis matrix* of $I$ is a matrix $M \in \operatorname{Mat}_{d \times d}(\mathbf{Z})$, such that the elements $(\alpha_1,\dotsc,\alpha_d)$ definied by \begin{align} \begin{pmatrix} \alpha_1 \\ \alpha_2 \\ \vdots \\ \alpha_d \end{pmatrix} = M_{\mathcal O} \begin{pmatrix} \omega_1 \\ \omega_2 \\ \vdots \\ \omega_d \end{pmatrix} \end{align} form a $\mathbf{Z}$-basis of $I$.


Let $(r,s)$ be the signature of $K$, that is, $K$ has $r$ real embeddings $\sigma_i \colon K \to \mathbf{R}$, $1 \leq i \leq r$, and $2s$ complex embeddings $\sigma_i \colon K \to \mathbf{C}$, $1 \leq i \leq 2s$. We order the complex embeddings such that $\sigma_i = \overline{\sigma_{i+s}}$ for $r + 1 \leq i \leq r + s$. The $\mathbf{Q}$-linear function \[ K \longrightarrow \mathbf R^{d}, \ \alpha \longmapsto (\sigma_1(\alpha),\dotsc,\sigma_r(\alpha),\sqrt{2}\operatorname{Re}(\sigma_{r+1}(\alpha)),\sqrt{2}\operatorname{Im}(\sigma_{r+1}(\alpha)),\dotsc,\sqrt{2}\operatorname{Re}(\sigma_{r+s}(\alpha)),\sqrt{2}\operatorname{Im}(\sigma_{r+s}(\alpha)) \] is called the **Minkowski map** (or **Minkowski embedding**). For our maximal order $\mathcal O$ with basis $\omega_1,\dotsc,\omega_d$, the matrix \[ \begin{pmatrix}  \sigma_1(\omega_1) & \dotsc & \sigma_r(\omega_1) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_1)) & \sqrt{2}\operatorname{Im}(\sigma_{r+1}(\omega_1)) & \dotsc & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_1)) \\
\sigma_1(\omega_2) & \dotsc & \sigma_r(\omega_2) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_2)) & \sqrt{2}\operatorname{Im}(\sigma_{r+1}(\omega_2)) & \dotsc  & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_2)) \\
\vdots & \dotsc & \vdots & \vdots & \dotsc & \vdots & \vdots\\
\sigma_1(\omega_d) & \dotsc & \sigma_r(\omega_d) & \sqrt{2}\operatorname{Re}(\sigma_{r+1}(\omega_d)) & \sqrt{2}\operatorname{Im}(\sigma_{r+2}(\omega_d)) & \dotsc & \sqrt{2}\operatorname{Im}(\sigma_{r+s}(\omega_d)) \end{pmatrix} \in \operatorname{Mat}_{d\times d}(\mathbf R). \] is called the **Minkowski matrix** of $\mathcal O$.

