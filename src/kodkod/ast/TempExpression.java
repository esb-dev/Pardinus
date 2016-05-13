/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.ast;


import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/** 
 * @author Eduardo Pessoa, nmm
 */
public final class TempExpression extends Expression {
    private final Expression expression;
    private final ExprOperator op;
    private final int arity;
    
    /**  
     */
    TempExpression(ExprOperator op, Expression child) {
        if (!(op == ExprOperator.POST)) {
            throw new IllegalArgumentException("Not a temporal operator: " + op);
        }
        this.expression = child;
        this.op = op;
        this.arity = child.arity();
    }

    /**
     * Returns the arity of this expression.
     * @return this.arity
     * @see kodkod.ast.Expression#arity()
     */
    public int arity() {
        return arity;
    }
    
    /**
     * Returns this.expression.
     * @return this.expression
     */
    public Expression expression() {return expression;}
    
    /**
     * Returns this.op.
     * @return this.op
     */
    public ExprOperator op() {return op;}
    
    
	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Expression#accept(kodkod.ast.visitor.ReturnVisitor)
	 */
	public <E, F, D, I> E accept(ReturnVisitor<E, F, D, I> visitor) {
		return visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
	 */
	public void accept(VoidVisitor visitor) {
		visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#toString()
     *
     *  post operator toString.
	 */ 
    public String toString() {
    	return expression.toString()+op.toString(); //pt.uminho.haslab: postfix 
    }   
}
