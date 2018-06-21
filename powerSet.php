<?php
/* How to run this code:

    include ("./powerSet.php");
    $P=new powerSet();
    $pda=$P->getPDA();
    $pda->parse( new lexer() );

 */
/* These lists and the lexer are here for testing 
 * Add a .y file parser and input scanner to complete */
$nTermList=array( 'A'=>true,'B'=>true,'D'=>true );
$termList=array( 'c'=>true,'e'=>true );
$grammar=array(
    new CFGRule( 0, 'S', array( 'A' )      ),
    new CFGRule( 1, 'A', array( 'B','B' )  ),
    new CFGRule( 2, 'B', array( 'D' )      ),
    new CFGRule( 3, 'D', array( 'c','D' )  ),
    new CFGRule( 4, 'D', array( 'e' )      )
);
class lexer{
    protected $input, $count;
    function __construct(){
        $this->count=-1;
        $this->input=array( 'c','c','e','e' );
    }
    function next(){
        $this->count++;
        return ( $this->count<count( $this->input ) )? 
            $this->input[$this->count] : false;
    }
}
/* Objects for grammar array. Used in powerset construction */
class CFGRule{
    public $ruleId, $LHS, $RHS, $len, $pos, $featured, $eps, $neps, $reduce, $shiftTo;
    function __construct( $setRuleId, $setLHS, $setRHS, $setPos=0, $setParent=null ){
        $this->ruleId=$setRuleId; 
        $this->LHS=$setLHS; 
        $this->RHS=$setRHS;
        $this->pos=$setPos;//                   the dot 
        $this->par=$setParent;//                see this->prepareStates()
        $this->len=count( $this->RHS );
        $this->shiftTo=0;//                     state after terminal symbol shift
        if( $setPos===0 ){
            $this->featured=$this->RHS[$setPos];
            $this->reduce=false;
        }
        else if( $setPos < $this->len ){
            $this->featured=$this->RHS[$setPos];
            $this->reduce=false;
        }
        else{
            $this->featured='';
            $this->reduce=true;
        }
        $this->eps=array();//                   epsilon successors
        $this->neps=array();//                  non-epsilon successors
    }
    function createSuccessor( $setPos ){
        return new CFGRule( $this->ruleId, $this->LHS, $this->RHS, $setPos, $this );
    }
    function setEps( $P ){
        if( !count( $this->eps ) ){
            $this->eps=array( $this );
            $eSuccessors=$P->find( $this->featured, 0 );
            foreach( $eSuccessors as $ekey=> $successor ){
                foreach( $successor->setEps( $P ) as $skey=> $sReach ){
                    $this->eps[]=$sReach;
                }
            }
        }
        return $this->eps;
    }
    function setNeps( $P ){
        if( !$this->reduce AND !count( $this->neps ) ){
            $nSuccessors=$P->find( $this->LHS, $this->pos+1 );
            foreach ( $nSuccessors as $prod ) {
                if( $this->ruleId == $prod->ruleId ){//same rule
                    foreach( $prod->eps as $sReach ){
                        $this->neps[]=$sReach;
                    }
                }
            }
        }
    }
    function disp( $dot=true ){
        $t1='&nbsp;&nbsp;&nbsp;&nbsp;';
        $t2=$t1.$t1;
        echo "$t1 [$this->LHS -> ";
        for ($i = 0; $i < count( $this->RHS ); $i++){
            if( $dot AND $i==$this->pos ){ echo ' * '; }
            else{ echo ' '; }
            echo $this->RHS[$i];
        }
        if( $dot AND $i==$this->pos ){ echo ' *'; }
        echo "]$t1";
//        if( $this->reduce ){
//            echo "$t1'r'$t1";
//            echo "($this->ruleId)$t1";
//        }
//        else{
//            echo "$t1 '$this->featured' $t1";
//            echo "($this->shiftTo)$t1"; 
//        }
    }
    function dispEps(){
        $label=( count( $this->eps ) )? 'eps':'No eps';
        echo "$label: ";
        for ($i = 0; $i < count( $this->eps ); $i++){
            $this->eps[$i]->disp();
        }
    }
    function dispNeps(){
        $label=( count( $this->neps ) )? 'neps':'No neps';
        echo "$label: ";
        for ($i = 0; $i < count( $this->neps ); $i++){
            $this->neps[$i]->disp();
        }
    }
}
/* Generate the PDA table using a powerset construction. */
class powerSet{//dependencies: $nTermList;$termList;$grammar;
    protected $indexed, $longest, $pda, $q1;
    function __construct( $zeroOrOne=1 ) {
        $this->q1=$zeroOrOne;//indexing scheme for states
        self::dispGrammar();
        self::maxLen_RHS();
        self::setIndexed();
        self::setESuccessors();
        self::setNonESuccessors();
        self::setTable( self::prepareStates() );
        //self::dispIndexed();
        self::dispDFA();
        $this->pda->dispTable();
    }
    protected function maxLen_RHS(){
        global $grammar;
        $this->longest=0;
        foreach ( $grammar as $prod ) {
            if( $prod->len > $this->longest ){
                $this->longest=$prod->len;
            }
        }
    }
    protected function setIndexed(){
        /* Rearrange grammar, adding successors.  
         * 2-d array, outer index is dot position ( Run dispIndexed() to view )*/
        global $grammar;
        $last=0;//allow for varied lengths
        $this->indexed=array();
        $this->indexed[0]=array();
        foreach ( $grammar as $prod ) {
            $this->indexed[0][]=$prod;
        }
        for ($i = 1; $i <= $this->longest; $i++) {
            $this->indexed[$i]=array();
            foreach ( $this->indexed[$last] as $prod ) {
                if( $prod->len >= $i ){
                    $last=$i;
                    $this->indexed[$i][]=$prod->createSuccessor( $i );
                }
            }
        }
    }
    function find( $needle, $pos ){//limits search by dot position
        $out=array();
        if( $pos<=$this->longest ){
            foreach ( $this->indexed[$pos] as $prod ) {
                if( $prod->LHS==$needle ){
                    $out[]=$prod;
                }
            } 
        }
        return $out;//list of rules with same LHS
    }
    protected function setESuccessors(){
        /* Call rule objects to set their own e-successor lists */
        for($i = 0; $i <= $this->longest; $i++){
            for($j = 0; $j < count( $this->indexed[$i] ); $j++){
                $this->indexed[$i][$j]->setEps( $this );
            }
        }
    }
    protected function setNonESuccessors(){
        for($i = 0; $i < $this->longest; $i++){
            for($j = 0; $j < count( $this->indexed[$i] ); $j++){
                $this->indexed[$i][$j]->setNeps( $this );
            }
        }
    }
    protected function prepareStates(){//set the 'shiftTo' field in base rule
        $count=$this->q1;
        foreach( $this->indexed[0][0]->eps as $prod ){
            if( $prod->par ){
                //echo "par on 0<br>";//
                $prod->par->shiftTo=$count;
            }
        }
        for ($i = 0; $i < count( $this->indexed ); $i++) {
            for ($j = 0; $j < count( $this->indexed[$i] ); $j++) {
                if( count( $this->indexed[$i][$j] ->neps ) ){
                    $count++;
                    foreach ( $this->indexed[$i][$j]->neps as $prod ) {
                        if( $prod->par ){
                            $prod->par->shiftTo=$count;//this sets state change
                        }
                    }
                }
            } 
        }
        return $count+(!$this->q1);//count is number of states
    }
    protected function setTable( $numStates ){
        /* This initializes the PDA table by calling pda->prepareState to 
         * set row fields. */
        $this->pda = new PDA( $numStates, $this->q1 );
        $count=$this->q1;
        foreach( $this->indexed[0][0]->eps as $prod ){
            if( $prod->reduce ){
                $this->pda->prepareState( $count, 'reduce', $prod->ruleId );
            }
            else{
                $this->pda->prepareState( $count, $prod->featured, $prod->shiftTo );
            }
        }
        for ($i = 0; $i < count( $this->indexed ); $i++) {
            for ($j = 0; $j < count( $this->indexed[$i] ); $j++) {
                if( count( $this->indexed[$i][$j]->neps ) ){
                    $count++;
                    foreach ( $this->indexed[$i][$j]->neps as $prod ) {
                        if( $prod->reduce ){
                            $this->pda->prepareState( $count, 'reduce', $prod->ruleId );
                        }
                        else{
                            $this->pda->prepareState( $count, $prod->featured, $prod->shiftTo );
                        }
                    }
                }
            } 
        }
    }
    function getPDA(){
        return $this->pda;
    }
    function dispGrammar(){
        global $grammar;
        echo "Disp Grammar:<br>";
        for ($i = 0; $i < count( $grammar ); $i++) {
            //echo "@ $i<br>";
            $grammar[$i]->disp( false );
            ///$grammar[$i]->dispEps();
            //$grammar[$i]->dispNeps();
            echo "<br>";
        } 
    }
    function dispIndexed(){
        echo "<br>Disp Indexed:<br>";
        for ($i = 0; $i < count( $this->indexed ); $i++) {
            echo "@ $i<br>";
            for ($j = 0; $j < count( $this->indexed[$i] ); $j++) {
                $this->indexed[$i][$j]->disp();
                //$this->indexed[$i][$j]->dispEps();
                //$this->indexed[$i][$j]->dispNeps();
                echo "<br>";
            } 
        }  
    }
    function dispDFA(){
        $count=$this->q1;
        echo "<br>Disp DFA:<br>$count: ";
        foreach ( $this->indexed[0][0]->eps as $prod ) {
            $prod->disp();
        }
        echo "<br>";
        for ($i = 0; $i < count( $this->indexed ); $i++) {
            for ($j = 0; $j < count( $this->indexed[$i] ); $j++) {
                if( count( $this->indexed[$i][$j] ->neps ) ){
                    $count++;
                    echo "$count: ";
                    foreach ( $this->indexed[$i][$j]->neps as $prod ) {
                        $prod->disp();
                    }
                    echo "<br>";
                }
            } 
        }  
    }

}
/* An LR(0) Parser */
class PDA{//dependencies: $nTermList;$termList;$grammar;
    public $q1, $startSymb, $table, $rList, $lex, $state, $stack;
    function __construct( $numStates, $zeroOrOne ){
        global $grammar;
        $this->q1=$zeroOrOne;//indexing scheme for states
        $this->startSymb=$grammar[0]->LHS;//indexing scheme for states
        self::prepareTable( $numStates );
    }
    function prepareTable( $numStates ){
        global $termList; global $nTermList;
        $tRow=array( 'reduce'=>false );
        foreach( $termList as $term=>$value ){
            $tRow[$term]=false;
        }
        foreach( $nTermList as $nTerm=>$value ){
            $tRow[$nTerm]=false;
        }
        $this->table=array();
        for ($i = $this->q1; $i < $numStates+$this->q1; $i++) {
            $this->table[$i]=$tRow;
        }
    }
    function prepareState( $index, $item, $value ){
        $this->table[$index][$item]=$value;
    }
    function getReduce(){//if reduce, returns ruleId
        $this->state=$this->stack[count( $this->stack )-1];//stack top
        return ( $this->table[$this->state]['reduce']===false )? 
            false : $this->table[$this->state]['reduce'];
    }
    function getState( $curr ){//read next state from table
        return ( isset( $this->table[$this->state][$curr] ) )? 
            $this->table[$this->state][$curr]: false;
    }
    function reduce( $reduce ){
        global $grammar;//for dev: display reduction without dot marker
        echo "&nbsp;&nbsp;&nbsp;&nbsp;Reduce"; $grammar[ $reduce ]->disp(false); 
        $len=$grammar[ $reduce ]->len;
        for($i = 0; $i < $len; $i++){//pop length of grammar
            array_pop( $this->stack );
        }
        $this->state=$this->stack[count( $this->stack )-1];//get pre-production state
        return $grammar[ $reduce ]->LHS;
    }
    function parse( $setLexer ){
        $this->lex=$setLexer;
        $this->stack=array( $this->q1 );//  init stack with start state
        $this->state=$this->q1;         //  state = stack top
        self::dispStack("<br>stack start: ");
        $curr=$this->lex->next();       //  same as calling yylex()
        $shift; $reduce;
        while( true ){
            /* Check in order: stack, halt, eat input */
            if( ( $reduce=self::getReduce() )!==false ){//case: reduce
                $LHS=self::reduce( $reduce );
                if(//case: push the reduction
                    $LHS!=$this->startSymb AND 
                    ( $shift=self::getState( $LHS ) )!==false 
                ){
                    $this->stack[]=$shift;
                }
            }
            else if( $curr===false OR !count( $this->stack ) ){//halt
                //echo "<br>completed: ";
                break;
            }
            else if( ( $shift=self::getState( $curr ) )!==false ){//case: push a terminal
                $this->stack[]=$shift;
                $curr=$this->lex->next();
            }
            else{
                echo "<br>error: symbol: $curr<br>";
                break;
            }
            self::dispStack("<br>"); 
        }
        self::dispStack("<br>stack end: "); echo "<br>";
    }
    function dispTable(){
        global $termList; global $nTermList;
        echo "<br>Disp Transition Table:<br>";
        echo "<table>";
        echo '<tr><th>States</th><th>|</th><th>Reduce</th><th>|</th>';
        foreach( $termList as $term=>$value ){
            echo "<th>$term</th>";
        }
        echo "<th>|</th>";
        foreach( $nTermList as $nTerm=>$value ){
            echo "<th>$nTerm</th>";
        }
        echo '</tr>';
        for($i = $this->q1; $i < count( $this->table )+$this->q1; $i++){
            $x=( $this->table[$i]['reduce']===false )? '&nbsp;' :  $this->table[$i]['reduce'];
            echo "<tr><th>$i</th><th>|</th><th>$x</th><th>|</th>";//
            foreach( $termList as $term=>$value ){
                $x=( $this->table[$i][$term]===false )? '&nbsp;' :  $this->table[$i][$term];
                echo "<td>$x</td>";
            }
            echo "<th>|</th>";
            foreach( $nTermList as $nTerm=>$value ){
                $x=( $this->table[$i][$nTerm]===false )? '&nbsp;' :  $this->table[$i][$nTerm];
                echo "<td>$x</td>";
            }
            echo '</tr>';
        }
        echo "</table><br>";
    }
    function dispStack( $label='' ){
        echo $label."(".implode( ', ', $this->stack ).")";
    }
}
?>
