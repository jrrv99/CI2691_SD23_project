import java.util.Random;
// import java.awt.Font;
// import java.util.Scanner;

public class LineasRectangulosColores {
    /******************************************************/
    /********************** GLOBALES **********************/
    /******************************************************/

    public static final int DEFAULT_TABLERO_SIZE = 9;
	public static int[][] tablero = new int[DEFAULT_TABLERO_SIZE][DEFAULT_TABLERO_SIZE];

    /**
     * Enum for objects representation in array indexes
     * constantes para la representacion de los objetos 
     * TODO: Use Enum DSE for good practices
     * TODO: CANTIDAD_DE_OBJS_EXISTENTES = Objetos.values().length
     */
    public static final int EMPTY_SLOT = -1; // Cuadro vacio en el tablero
    public static final int CUADRADO = 0;
    public static final int BOLA_ROJA = 1;
    public static final int BOLA_AZUL = 2;
    public static final int BOLA_VERDE = 3;
    public static final int BOLA_NARANJA = 4;
    public static final int BOLA_MAGENTA = 5;
    public static final int BOLA_AMARILLA = 6;
    public static final int CANTIDAD_DE_OBJS_EXISTENTES = 7; // cantidad de objetos cuadrado mas 6 circulos

    /**
     * contador_de_objetos: Representa la cantidad de cada objeto en el
     * tablero, y el indice corresponde al valor del objeto representado en
     * las constantes.
     * 
     * DEFAULT_PROXIMOS_OBJETOS_CANTIDAD: Guarda la cantidad de objetos a
     * agregar por defecto.
     * 
     * proximosObjetos: guarda los proximos objetos a agregar en el tablero es
     * un array de enteros del 0 al DEFAULT_PROXIMOS_OBJETOS_CANTIDAD
     */
    public static int[] contador_de_objetos = {0, 0, 0, 0, 0, 0, 0};
    public static final int DEFAULT_PROXIMOS_OBJETOS_CANTIDAD = 3;
    public static int[] proximosObjetos = new int[DEFAULT_PROXIMOS_OBJETOS_CANTIDAD];

    /**
     * casillas: se almacenaran las casillas vacias seleccionadas de forma aleatorea.
     * FILA: indice para la fila en la estructura casilla
     * COLUMNA: indice para la columna en la estructura casilla
     *
     * Lo declaro aca para poder usarlo en la postcondicion.
     */
    public static final int FILA = 0; 
    public static final int COLUMNA = 1;
    public static int[][] casillas = new int[DEFAULT_PROXIMOS_OBJETOS_CANTIDAD][2];

    /**
     * Constantes y variables para la configuracion del Panel
     */
    public static final int PANEL_BARRA_TITULO_ALTURA = 38; // alto de la barra de titulo 
    public static final int PANEL_DEFAULT_XMAX = 512;
    public static final int PANEL_DEFAULT_YMAX = 512;
    public static final String PANEL_DEFAULT_TITLE = "Lineas Rectangulos Colores";
    
    public static int PANEL_YMAX = PANEL_DEFAULT_YMAX;
    public static int PANEL_XMAX = PANEL_DEFAULT_XMAX;

    /*****************************************************************/
    /*************************** UTILITIES ***************************/
    /*****************************************************************/

    // Retorna un entero entre 0 y n es decir [0, n]
    /*@ requires 0 < n <= Integer.MAX_VALUE;
      @ ensures 0 <= \result <= n;
      @*/
    public static /*@ pure @*/ int getRandomInt(int n) {
        Random random = new Random();
        return random.nextInt(n + 1);
    }

    // Se suma el alto de la barra del titulo para normalizar el cuerpo del panel
    /**
     * Dado que cuando se abre, la ventana, el YMAX lo toma desde el inicio de la
     * ventana, no desde el punto (0,0), hay que sumarle la altura de la barra del
     * titulo al PANEL_YMAX para normalizar la altura del panel editable.
     */
    /*@ requires true;
      @ ensures \result == (PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA);
      @*/
    public static /*@ pure @*/ int normalizedPanelYMAX() {
        return PANEL_YMAX + PANEL_BARRA_TITULO_ALTURA;
    }

    /********************************************************************/
    /************************* LOGICA DEL JUEGO *************************/
    /********************************************************************/

    /**
     * Retorna el objeto en menor cantidad el el objeto. En este caso el indice
     * corresponde al valor que representa el objeto
     *
     * @return int
     */
    /*@ requires contador_de_objetos != null;
      @ requires (\forall int i; 0 <= i && i < contador_de_objetos.length; 0 <= contador_de_objetos[i] <= Integer.MAX_VALUE);
      @ ensures (\forall int i; 0 <= i && i < contador_de_objetos.length; contador_de_objetos[\result] <= contador_de_objetos[i]);
      @*/
    public static /*@ pure @*/ int obtenerObjEnMenorCantidad() {
        int i = 1, menor = 0;

        while (i < contador_de_objetos.length) {
            if (contador_de_objetos[i] < contador_de_objetos[menor])
                menor = i;
            i++;
        }

        return menor;
    }

    /**
     * Procedimiento 2: Obtiene los proximos elementos a agregar y los guarda
     * en proximosObjetos. Los dos primeros son random, y el ultimo es el que
     * se encuentra en menor cantidad en el tablero.
     */
    /*@ requires proximosObjetos != null;
      @ ensures \forall int i; 0 <= i && i < proximosObjetos.length; 0 <= proximosObjetos[i] && proximosObjetos[i] < CANTIDAD_DE_OBJS_EXISTENTES;
      @*/
    public static /*@ pure @*/ void obtenerProximosObjetos() {
        proximosObjetos[0] = getRandomInt(CANTIDAD_DE_OBJS_EXISTENTES - 1);  // -1 porque retorna [0, n]
        proximosObjetos[1] = getRandomInt(CANTIDAD_DE_OBJS_EXISTENTES - 1);  // -1 porque retorna [0, n]
        proximosObjetos[2] = obtenerObjEnMenorCantidad();
    }

    /**
     * Retorna simplemente si la casilla está marcada como vacia es decir si
     * el valor es EMPTY_SLOT (-1)
     *
     * @param fila valor de la fila de la casilla
     * @param columna valor de la columna de la casilla
     * @return (boolean) retorna si la casilla esta vacia
     */
    /*@ requires tablero != null;
      @ requires 0 <= fila < DEFAULT_TABLERO_SIZE;
      @ requires 0 <= columna < DEFAULT_TABLERO_SIZE;
      @ ensures \result <==> tablero[fila][columna] == EMPTY_SLOT;
      @*/
    public static /*@ pure @*/ boolean esCasillaVacia(int fila, int columna) {
        return tablero[fila][columna] == EMPTY_SLOT;
    }

    /**
     * Asigna la fila y la columna de una casilla vacia de manera aleatoria
     * 
     * TODO: improve algorithm performance by adding a global counter with the
     * TODO: empty slots amount and getting all this slots in an array of this
     * TODO: counter size and returning a random index of this array
     * * Este refactor del counter se puede hacer sumando los objetos presentes
     * * en el tablero es decir sumar el array los valores del array
     * * contador_de_objetos y restandoselo al total de slots DEFAULT_TABLERO_SIZE x DEFAULT_TABLERO_SIZE
     */
    /*@ requires casilla != null;
      @ ensures 0 <= casilla[FILA] < DEFAULT_TABLERO_SIZE;
      @ ensures 0 <= casilla[COLUMNA] < DEFAULT_TABLERO_SIZE;
      @ ensures esCasillaVacia(casilla[FILA], casilla[COLUMNA]);
      @*/
    public static /*@ pure @*/ void obtenerCasillaRandomVacia(int[] casilla) {
        /**
         * Tecnica de elmininacion de un predicado de una conjunción
         * Cota: no hay una cota exacta, al ser numeros random depende de la aleatoriedad para conseguir la casilla vacia.
         */
        /*@ maintaining 0 <= casilla[FILA] < DEFAULT_TABLERO_SIZE;
          @ maintaining 0 <= casilla[COLUMNA] < DEFAULT_TABLERO_SIZE;
          @*/
        do {
            casilla[FILA] = getRandomInt(DEFAULT_TABLERO_SIZE - 1);  // -1 porque retorna [0, n]
            casilla[COLUMNA] = getRandomInt(DEFAULT_TABLERO_SIZE - 1);  // -1 porque retorna [0, n]
        } while (!esCasillaVacia(casilla[FILA], casilla[COLUMNA]));
    }

    /**
     * Aumenta la cantidad de un objeto en el tablero
     * @param objeto - valor representativo del objeto en las estructuras de array
     * @param cantidad - cantidad a aumentar en el array contador_de_objetos
     */
    /*@ requires 0 <= objeto <= CANTIDAD_DE_OBJS_EXISTENTES;
      @ requires 0 < cantidad <= DEFAULT_TABLERO_SIZE*DEFAULT_TABLERO_SIZE;
      @ ensures contador_de_objetos[objeto] == (\sum int i; 0 <= i && i < DEFAULT_TABLERO_SIZE; (\num_of int j; 0 <= j && j < DEFAULT_TABLERO_SIZE; tablero[i][j] == objeto));
      @*/
    public static /*@ pure @*/ void aumentarCantidadDeObjeto(int objeto, int cantidad) {
        contador_de_objetos[objeto] += cantidad;
    }

    /**
     * Agrega los proximos objetos en casillas vacias en el tablero
     * seleccionadas de manera aleatorea. 
     */
    /*@ requires tablero != null;
      @ requires proximosObjetos != null;
      @ requires (\forall int i; 0 <= i && i < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD; 0 <= proximosObjetos[i] && proximosObjetos[i] < CANTIDAD_DE_OBJS_EXISTENTES);
      @ ensures (\forall int k; 0 <= k && k < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD; tablero[casillas[k][FILA]][casillas[k][COLUMNA]] == proximosObjetos[k]);
      @*/
    public static /*@ pure @*/ void agregarProximosObjetos() {
        int i = 0;

        /*@ maintaining 0 <= i <= DEFAULT_PROXIMOS_OBJETOS_CANTIDAD;
          @ maintaining (\forall int k; 0 <= k && k < i; tablero[casillas[k][FILA]][casillas[k][COLUMNA]] == proximosObjetos[k]);
          @ decreasing DEFAULT_PROXIMOS_OBJETOS_CANTIDAD - i;
          @*/
        while (i < DEFAULT_PROXIMOS_OBJETOS_CANTIDAD) {
            obtenerCasillaRandomVacia(casillas[i]);
            // Colocar el objeto en la casilla vacia al azar en la posicion i de las casillas 
            tablero[casillas[i][FILA]][casillas[i][COLUMNA]] = proximosObjetos[i];
            // aumentar la cantidad del objeto que agrega en el tablero
            aumentarCantidadDeObjeto(proximosObjetos[i], 1);

            i++;
        }
    }

    /**
     * Procedimiento 1: inicializa el tablero colocando los espacios vacios y
     * los 3 primeros objetos
     *
     * * En la postcondicion se evalua que se hayan agregado la cantidad inicial
     * * de objetos que por defecto es DEFAULT_PROXIMOS_OBJETOS_CANTIDAD.
     */
    /*@ requires tablero != null;
      @ requires proximosObjetos != null;
      @ ensures DEFAULT_PROXIMOS_OBJETOS_CANTIDAD == (\sum int i; 0 <= i && i < DEFAULT_TABLERO_SIZE; (\num_of int j; 0 <= j && j < DEFAULT_TABLERO_SIZE; tablero[i][j] != EMPTY_SLOT));
      @*/
	public static /*@ pure @*/ void inicializarTablero() {
        int fila = 0, columna;

        /*@ maintaining 0 <= fila <= DEFAULT_TABLERO_SIZE;
          @ decreasing DEFAULT_TABLERO_SIZE - fila;
          @*/
        while (fila < DEFAULT_TABLERO_SIZE) {
            columna = 0;

            /*@ maintaining 0 <= columna <= DEFAULT_TABLERO_SIZE;
              @ maintaining (\forall int i; 0 <= i && i < fila; (\forall int j; 0 <= j && j < columna; tablero[i][j] == EMPTY_SLOT));
              @ decreasing DEFAULT_TABLERO_SIZE - columna;
              @*/
            while (columna < DEFAULT_TABLERO_SIZE) {
                tablero[fila][columna] = EMPTY_SLOT;
                columna++;
            }
            fila++;
        }
        obtenerProximosObjetos();
        agregarProximosObjetos();
    }

    public static void main(String[] args) {
        // MaquinaDeTrazados panel = new MaquinaDeTrazados(
        //     PANEL_XMAX,
        //     normalizedPanelYMAX(),
        //     PANEL_DEFAULT_TITLE,
        //     Colores.LIGHT_GRAY
        // );
        inicializarTablero();

        for (int i =0; i < contador_de_objetos.length; i++) {
            obtenerProximosObjetos();
            agregarProximosObjetos();
        }

        Utils.imprimirTableroPorConsola(tablero, DEFAULT_TABLERO_SIZE);
    }
}