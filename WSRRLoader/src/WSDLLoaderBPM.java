import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.net.Authenticator;
import java.net.HttpURLConnection;
import java.net.PasswordAuthentication;
import java.net.URL;
import java.net.URLEncoder;
import java.text.MessageFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.net.ssl.HostnameVerifier;
import javax.net.ssl.HttpsURLConnection;
import javax.net.ssl.SSLSession;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpression;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.apache.commons.codec.binary.Base64;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.xml.sax.SAXException;

import com.ibm.serviceregistry.sdo.helper.PropertyConstants;

import teamworks.TWList;

/**
 * Loads a CSV file containing service information and pushes it into Service Registry using the REST API.
 */
public class WSDLLoaderBPM {
	
	public WSDLLoaderBPM() {
		//19092016 + MQ
		//05102016 aggiunto campo abilitazione infrastrutturale
		//06102016 aggiunta interfaccia CALLABLE
		//26102016 modifica al mqmanual per portare il nome coda in sm63_requestQName
		//-->Fork da IXPG0
		//01122016 inseriti nuovi campi come da richiesta ISP x aderire alla versione 6.5.1 tolte poi scrittura cpy_cobol (07/12/16)
		//17122016 inseriti campi per reps0 e altri campi per aderire alle nuove specifiche del modello (x i cambiamenti vedere quanto fatto per reps0)
        //20122916 inseritocampo SOPEN/SCOPEN gep63_SOPEN_USO_SICUREZZA e gep63_SCOPEN_USO_SICUREZZA e i relativi per SHOST/SCHOST
		//040107  tolti i campi SOPEN/SCOPEN gep63_SOPEN_USO_SICUREZZA e gep63_SCOPEN_USO_SICUREZZA SCHOST/SHOST
		//040107 nella posizione dove venivano valoirizzati : gep63_SOPEN_USO_SICUREZZA e gep63_SCOPEN_USO_SICUREZZA ora
		//       ora inserisco i nuovi campi: gep63_SOPEN_EAR_SERVIZIO e gep63_SCOPEN_EAR_SERVIZIO
		//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
		//040117 se interfaccia SCH passo endpoint null nella creazione SLD
	    //060117 inserito sm63_ERRORE_GENERAZIONE_WSPROXY ="" di default su endpointproxy
		//110117 gep63_TIPO_SERVIZIO diventa gep63_TIPOLOGIA
		//110117 gep63_FLG_CTRL_TIPO_SERVIZIO diventa gep63_FLG_CTRL_TIPOLOGIA
		//02022017 se BS o MPE la versione viene presa dal campo a video: tipo interfaccia
		//21022017 inserita la versione nella creazione di createCicsEndpointXMLDAta
		//23022017 inseriti nuovi campi vedi nel codice
		//08032017 inserito metodo per creazione SLA
		//08032017 + gep63_DOC_ANALISI_DETTAGLIO + gep63_SECURITY_ROLE
		//08032017 aggiungo il campo sm63_ESPOSTO_COME_API nell endpointRest
		//11032017 creato createZResEndpointXMLDAta e createWola...
		//31032017 i campi ora arrivano in input gep63_DERIVANTE_DA_ALTRI_SERV - gep63_TIPOLOGIA_OGGETTO_ESISTENTE - gep63_NOME_SERVIZIO_PRECEDENTE 
        //02/05/2017 propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
        //10052017 propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_MD_X_INTEROPER", "Y1BP0CMB"));
		//12052017 propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_MD_X_INTEROPER", "Y1BP0CMB"));
		//281117 aggiungo alla fine dei parametri anche la versione ad esclusione di SCHOST
		//18052017 propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_MD_X_INTEROPER", "")); propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_MD_X_INTEROPER", ""));
		//281117 aggiungo alla fine dei parametri anche la versione ad esclusione di SCHOST
		//170118 passo anche a questo metodo la versione in modo che sia allineato con gli altri
		//230118 aggiunti gep63_SOPEN_ABILITAZ_WRITE gep63_SOPEN_ABILITAZ_READ gep63_SOPEN_MOD_UTENTI_BUS
	}
    /* The CSV file that will be loaded */
    private File csvFile = null;

    /* The path to the directory containing all the WSDL and XSD documents */
    private File wsdlPath = null;

    /* The hostname or IP address of the Service Registry server */
    private String hostname;

    /* The port of the Service Registry server, typically the WC_defaulthost port */
    private String port;

    // XML Processing Constants
    DocumentBuilderFactory docBuilderFactory = null;
    DocumentBuilder docBuilder = null;

    private XPathExpression valueAttrExpression = null;
    private static final String XPATH_EXPR_VALUE_ATTR = "//property/@value";

    // REST XML Element Name Constants
    private static final String ELEMENT_RESOURCES = "resources";
    private static final String ELEMENT_RESOURCE = "resource";
    private static final String ELEMENT_PROPERTIES = "properties";
    private static final String ELEMENT_PROPERTY = "property";
    private static final String ELEMENT_RELATIONSHIPS = "relationships";
    private static final String ELEMENT_RELATIONSHIP = "relationship";
    private static final String ELEMENT_CLASSIFICATIONS = "classifications";
    private static final String ELEMENT_CLASSIFICATION = "classification";

    // REST XML Attribute Name Constants
    private static final String ATTR_NAME = "name";
    private static final String ATTR_VALUE = "value";
    private static final String ATTR_TARGET_BSRURI = "targetBsrURI";
    private static final String ATTR_TARGET_TYPE = "targetType";
    private static final String ATTR_URI = "uri";
    private static final String ATTR_PRIMARY_TYPE = "primaryType";

    // WSRR Property Name Constants
    private static final String PROPERTY_ALE63_ASSET_WEB_LINK = "ale63_assetWebLink";
    private static final String PROPERTY_ALE63_FULL_DESCRIPTION = "ale63_fullDescription";
    private static final String PROPERTY_ALE63_REMOTE_STATE = "ale63_remoteState";
    private static final String PROPERTY_ALE63_ASSET_TYPE = "ale63_assetType";
    private static final String PROPERTY_ALE63_REQUIREMENTS_LINK = "ale63_requirementsLink";
    private static final String PROPERTY_ALE63_OWNER_EMAIL = "ale63_ownerEmail";
    private static final String PROPERTY_ALE63_GUID = "ale63_guid";
    private static final String PROPERTY_ALE63_COMMUNITY_NAME = "ale63_communityName";
    private static final String PROPERTY_ALE63_ASSET_OWNERS = "ale63_assetOwners";
    private static final String PROPERTY_GEP63_CONSUMER_IDENTIFIER = "gep63_consumerIdentifier";
    private static final String PROPERTY_GEP63_VERSION_AVAILABILITY_DATE = "gep63_versionAvailabilityDate";
    private static final String PROPERTY_GEP63_VERSION_TERMINATION_DATE = "gep63_versionTerminationDate";
    private static final String PROPERTY_GEP63_CONSUMER_IDENTIFIER_LOCATION = "gep63_consumerIdentifierLocationInfo";
    private static final String PROPERTY_GEP63_CONTEXT_IDENTIFIER_LOCATION = "gep63_contextIdentifierLocationInfo";
    
    private static final String PROPERTY_ALE63_CONTACT = "ale63_contact";
    private static final String PROPERTY_ALE63_CONTACT_EMAIL = "ale63_contactEmail";


    // WSRR Relationship Name Constants
    private static final String RELATIONSHIP_ALE63_DEPENDENCY = "ale63_dependency";
    private static final String RELATIONSHIP_ALE63_ARTIFACTS = "ale63_artifacts";
    private static final String RELATIONSHIP_ALE63_OWNING_ORGANIZATION = "ale63_owningOrganization";
    private static final String RELATIONSHIP_GEP63_SERVICE_INTERFACE_VERSIONS = "gep63_serviceInterfaceVersions";
    private static final String RELATIONSHIP_GEP63_CHARTER = "gep63_charter";
    private static final String RELATIONSHIP_GEP63_CAPABILITY_VERSIONS = "gep63_capabilityVersions";
    private static final String RELATIONSHIP_GEP63_CONSUMES = "gep63_consumes";
    private static final String RELATIONSHIP_GEP63_PROVIDES = "gep63_provides";
    private static final String RELATIONSHIP_GEP63_INTERFACE_SPECIFICATIONS = "gep63_interfaceSpecifications";
    private static final String RELATIONSHIP_GEP63_PROVIDED_WEB_SERVICES = "gep63_providedWebServices";
    private static final String RELATIONSHIP_GEP63_PROVIDED_REST_SERVICES = "gep63_providedRESTServices";
    private static final String RELATIONSHIP_GEP63_PROVIDED_SCA_MODULES = "gep63_providedSCAModules";
    private static final String RELATIONSHIP_GEP63_BOUND_SCA_EXPORT = "gep63_boundScaExport";
    private static final String RELATIONSHIP_GEP63_ANONYMOUS_SLA = "gep63_anonymousSLA";
    private static final String RELATIONSHIP_GEP63_CAMPATIBLE_SLDS = "gep63_compatibleSLDs";
    private static final String RELATIONSHIP_GEP63_BOUND_WEB_SERVICE_PORT = "gep63_boundWebServicePort";
    private static final String RELATIONSHIP_GEP63_BOUND_REST_SERVICE = "gep63_boundRESTService";
    private static final String RELATIONSHIP_GEP63_SERVICE_INTERFACE = "gep63_serviceInterface";
    private static final String RELATIONSHIP_GEP63_AVAILABLE_ENDPOINTS = "gep63_availableEndpoints";
    private static final String RELATIONSHIP_GEP63_AVAILABLE_OPERATIONS = "gep63_availableOperations";
    
    private static final String RELATIONSHIP_GEP63_CHILD_ORGANIZATIONS = "ale63_childOrganizations";

    // WSRR OWL URI Constants
    private static final String OWL_ORGANIZATION="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ALEModel#Organization";
    
    private static final String OWL_URI_BUSINESS_SERVICE = "http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#BusinessService";
    private static final String OWL_URI_SERVICE_VERSION = "http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#ServiceVersion";
    private static final String OWL_URI_SLD = "http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#ServiceLevelDefinition";
    private static final String OWL_URI_SLA = "http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceProfileExtensions#ServiceLevelAgreement";
    private static final String OWL_REST_INTERFACE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v8r0/RESTModel#RESTServiceInterface";

    private static final String OWL_REST_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v8r0/RESTModel#RESTServiceEndpoint";
    private static final String OWL_CALLABLE_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v8r0/RESTModel#CALLABLEServiceEndpoint";
    private static final String OWL_SOAP_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#SOAPServiceEndpoint";
    private static final String OWL_CICS_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#CICSServiceEndpoint";
    private static final String OWL_MQ_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#MQServiceEndpoint";
    private static final String OWL_MQ_ENDPOINT_MANUAL="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#ManualMQEndpoint";
    private static final String OWL_SERVICEPROXY_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#ProxyServiceEndpoint";
    private static final String OWL_ZRES_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#ZRESServiceEndpoint";
    private static final String OWL_WOLA_ENDPOINT="http://www.ibm.com/xmlns/prod/serviceregistry/v6r3/ServiceModel#WOLAServiceEndpoint";
    
     
    private static final String OWL_ENVIRONMENT_STATE="http://www.ibm.com/xmlns/prod/serviceregistry/6/1/GovernanceProfileTaxonomy#";
    private static final String OWL_INTERNAL_EXTERNAL_STATE="http://www.ibm.com/xmlns/prod/serviceregistry/8/0/visibilitytaxonomy#";
    
    //ISP Object Definition - Business Service Extensions
    private static final String OWL_URI_ISP_SERVICE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#";
    private static final String OWL_URI_SOPEN_SERVICE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SOPENService";
    private static final String OWL_URI_SCOPEN_SERVICE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SCOPENService";
    private static final String OWL_URI_SCHOST_SERVICE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SCHOSTService";
    private static final String OWL_URI_SHOST_SERVICE="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SHOSTService";
  //ISP Object Definition - Business Service Version Extensions
    private static final String OWL_URI_ISP_SERVICE_VERSION="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#";
    private static final String OWL_URI_SOPEN_SERVICE_VERSION="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SOPENServiceVersion";
    private static final String OWL_URI_SCOPEN_SERVICE_VERSION="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SCOPENServiceVersion";
    private static final String OWL_URI_SCHOST_SERVICE_VERSION="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SCHOSTServiceVersion";
    private static final String OWL_URI_SHOST_SERVICE_VERSION="http://www.ibm.com/xmlns/prod/serviceregistry/profile/v6r3/GovernanceEnablementModel#SHOSTServiceVersion";
 

    // Misc. String Constants
    private static final String SLD_NAME_PREFIX = "SLD - ";
    private static final String SLD_DESCRIPTION = "Service Level Definition for version {0} of the {1}";
    private static final String REQUIREMENTS_DOC_DESCRIPTION = "Requirements document for the {0}";
    private static final String EMPTY_STRING = "";

    static {
        // Accept all https connections.
        // This is required is your conenction url uses https.
        // The default implementation is to reject all https connections.
        HttpsURLConnection.setDefaultHostnameVerifier(new HostnameVerifier() {
            public boolean verify(String hostname, SSLSession session) {
                return true;
            }
        });

        // Provide user and password to the Authenticator
        // Required if application security is on for the target Service Registry
        // Change "userid" and "password" to the correct login credentials
        // for your installation.
        Authenticator.setDefault(new Authenticator() {
            protected PasswordAuthentication getPasswordAuthentication() {
                return new PasswordAuthentication("gabriele", "viviana".toCharArray());
            }
        });
    }

    /**
     * This inner class is used by the loadDocument method that will throw this exception if another document must be
     * loaded first.
     */
    private class MustImportReferenceException extends Exception {
        /* The filename of the document that must be imported first */
        String filename;

        /**
         * Constructs a new exception class with the given filename
         * 
         * @param filename
         *            The filename of the document to import first
         */
        public MustImportReferenceException(String filename) {
            this.filename = filename;
        }

        /**
         * Gets the filename that must be imported first
         * 
         * @return The filename with extension, no path information
         */
        public String getFilename() {
            return this.filename;
        }
    }

    /**
     * Constructs a new WSDLLoader with the specified csv file, wsdl document path and Service Registry hostname and
     * port name.
     * 
     * @param csvFile
     *            The CSV file to load
     * @param wsdlPath
     *            The path of where all the WSDL and XSD documents will be found
     * @param hostname
     *            The hostname or IP address of the Service Registry server
     * @param port
     *            The port of the Service Registry server, typically the WC_defaulthost port
     */
    public WSDLLoaderBPM(File csvFile, File wsdlPath, String hostname, String port) throws Exception {
        this.csvFile = csvFile;
        this.wsdlPath = wsdlPath;
        this.hostname = hostname;
        this.port = port;

        try {
            docBuilderFactory = DocumentBuilderFactory.newInstance();
            docBuilder = docBuilderFactory.newDocumentBuilder();

            XPathFactory xPathFactory = XPathFactory.newInstance();
            XPath xPath = xPathFactory.newXPath();
            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
            throw e;
        } catch (XPathExpressionException e) {
            e.printStackTrace();
            throw e;
        }

    }

    /**
     * Command line interface to run the WSDLLoader application. Usage: WSDLLoader -csvFile <csvfile> -wsdlPath
     * <wsdlpath> -hostname <hostname> -port <port>
     * 
     * @param args
     *            List of arguments supplied by the command line, see usage for more information
     */
    public static void main(String[] args) throws Exception {
        // Initialize the config variables for processing from the command line
        File wsdlPath = new File(".");
        File csvFile = null;
        String hostname = "localhost";
        String port = "9443";

        // Iterate through each command line in groups of two to extract the parameter name and value
        for (int i = 0; i < args.length; i += 2) {
            if (args[i].equals("-csvFile") && i < args.length - 1) {
                csvFile = new File(args[i + 1]);
            }
            if (args[i].equals("-wsdlPath") && i < args.length - 1) {
                wsdlPath = new File(args[i + 1]);
            }
            if (args[i].equals("-hostname") && i < args.length - 1) {
                hostname = args[i + 1];
            }
            if (args[i].equals("-port") && i < args.length - 1) {
                port = args[i + 1];
            }
        }

        // If any of the command line arguments was missing, output the usage information
        if (wsdlPath == null || csvFile == null || hostname == null || port == null) {
            System.out.println("WSDLLoader -csvFile <csvfile> [-wsdlPath <wsdlpath> -hostname <hostname> -port <port>]");
            System.out.println("");
            System.out.println("  -csvFile full file name of the CSV file that will be imported");
            System.out.println("");
            System.out.println("  -wsdlpath full path to a directory containing the WSDL and XSD documents.");
            System.out.println("            Defaults to the current directory.");
            System.out.println("");
            System.out.println("  -hostname hostname or IP address to the Service Registry service.");
            System.out.println("            Defaults to localhost.");
            System.out.println("");
            System.out.println("  -port  Service Registry WC_defaulthost port. (WC_defaulthost port is the same port");
            System.out.println("         that the Service Registry Web UI is hosted on -- typically 9080/9443 in a");
            System.out.println("         standalone secure/unsecure environment). Defaults to 9433.");
            return;
        }

        System.out.println("csvFile: " + csvFile);
        System.out.println("wsdlPath: " + wsdlPath);
        System.out.println("hostname: " + hostname);
        System.out.println("port: " + port);

        // Initalize a new WSDL loader class with the command line parameters
        // The WSDLLoader.loadServices method is responsible for reading the services from the CSV
        // file and processing each service entry to POST it into Service Registry:
        WSDLLoaderBPM loader = new WSDLLoaderBPM(csvFile, wsdlPath, hostname, port);

        // Load all the services, any exceptions throws will be returned back to the console
        loader.loadServices();

        // Output a message to indicate that processing is complete
        System.out.println("Load complete");
    }

    /**
     * A basic method to read the contents of the CSV document. Note: This method is limited to cell values that are not
     * encapsulated by quotes and do not contain nested commas in the cell values.
     * 
     * @return An ArrayList representing each row in the CSV document. The value of each entry is a HashMap that maps
     *         each column name to the cell value. The column names are determined by the first row in the CSV document.
     * @throws IOException
     */
    private ArrayList<HashMap<String, String>> readCSV() throws IOException {
        // Initialize the services ArrayList ready for reading from the CSV file
        ArrayList<HashMap<String, String>> services = new ArrayList<HashMap<String, String>>();

        // Keep a simple array of the header fields from the first row
        String[] headers;

        // Read each line in the CSV file
        BufferedReader reader = new BufferedReader(new FileReader(this.csvFile));
        String line = reader.readLine();
        if (line != null) {
            // This is the first line, so assume it is the list of headers. Perform a
            // basic split based on the comma to extract the header value.
            headers = line.split(",");

            // Read the remaining data lines
            while ((line = reader.readLine()) != null) {
                // Perform a basic split based on the comma separation to extract the
                // cell values.
                String[] fields = line.split(",");

                /*
                 * Perform a little bit of validation here... make sure that the line being processed contains the
                 * expected number of values.
                 */
                if (fields.length == headers.length) {
                    HashMap<String, String> service = new HashMap<String, String>();

                    // Add service to our hash map
                    for (int i = 0, j = 0; i < headers.length && j < fields.length; i++, j++) {
                        System.out.println(headers[i] + " : " + fields[i]);
                        service.put(headers[i], fields[j]);
                    }
                    services.add(service);
                }
            }
        }

        return services;
    }

    /**
     * Using a service row HashMap, return the desired query parameter in the form of &amp;param=value, where value is
     * URL encoded in UTF-8. If the value is null in that the document did not contain the specified column heading, do
     * not return a query parameter, just an empty string.
     * 
     * @param service
     *            The HashMap representing the service record loaded from the CSV file
     * @param propertyName
     *            The property name to use for the query parameter
     * @param csvColumn
     *            The name of the CSV column to retrieve from the service record
     * @return Return the property in the form of &amp;param=value or empty string if there is not matching value
     * @throws UnsupportedEncodingException
     */
    private String generateProperty(HashMap<String, String> service, String propertyName, String csvColumn) throws UnsupportedEncodingException {
        String value = service.get(csvColumn);
        if (value == null) {
            return "";
        } else {
            return "&" + propertyName + "=" + URLEncoder.encode(value, "UTF-8");
        }
    }

    /**
     * Load all the services from the configured CSV file into Service Registry. Depending on the format of the source
     * CSV document, this method may require modification to lookup the relevant data.
     * 
     * @throws Exception
     */
    @SuppressWarnings("unchecked")
	public void loadServices() throws Exception {
        System.out.println("Loading WSDL Documents");

        // Read all the services from the CSV file into an ArrayList
        ArrayList<HashMap<String, String>> services = this.readCSV();

        // Add each services using the REST API
        Iterator<HashMap<String, String>> it = services.iterator();
        while (it.hasNext()) {
            HashMap<String, String> service = it.next();
            System.out.println("service size is = " + service.size());

            // Get the name of the WSDL file from the CSV document
            String wsdlFileName = service.get("WSDL Filename");
            System.out.println("WSDL Filename is= " + wsdlFileName);
            File wsdlFile = new File(this.wsdlPath, wsdlFileName);

            // Get the name of the WSDL file from the CSV document
            String requirementsDocFileName = service.get("Documentation Filename");
            System.out.println("Requirements Filename is = " + requirementsDocFileName);
            File requirementsFile = new File(this.wsdlPath, requirementsDocFileName);

            // Build a URL with all the properties that we want. Note the CSV column headers must be exact when using
            // generateProperty.
            // Any number of properties can be added to the query string as they will be treated as custom properties on
            // the document
            // when loaded into Service Registry.
            String params = "name=" + URLEncoder.encode(service.get("Name"), "UTF-8") + generateProperty(service, "description", "Description")
                + generateProperty(service, "version", "Version") + generateProperty(service, "Status", "Status")
                + generateProperty(service, "DateInProduction", "Date in Production") + generateProperty(service, "Owner", "Owner")
                + generateProperty(service, "EndpointURL", "Endpoint URL") + generateProperty(service, "DocumentationFilename", "Documentation Filename")
                + generateProperty(service, "WSDLFilename", "WSDL Filename");

            // Generate our master URL ready for POSTing WSDL documents to Service Registry.
            final String wsdlDocURL = "https://" + hostname + ":" + port + "/WSRR/8.5/Content/WSDLDocument?" + params;
            System.out.println("--------------------------------------------------------------------------------");
            System.out.println("queryURL is :" + wsdlDocURL);
            System.out.println("--------------------------------------------------------------------------------");
            System.out.println("wsdlFile is :" + wsdlFile);
            System.out.println("--------------------------------------------------------------------------------");

            // Load the WSDL document tree for this service entry.
            String wsdlDocBsrUri = this.loadDocumentTree(wsdlDocURL, wsdlFile);

            // Generate our master URL ready for POSTing WSDL documents to Service Registry.
            Object[] inserts = new Object[] { service.get("Name") };
            String description = MessageFormat.format(REQUIREMENTS_DOC_DESCRIPTION, inserts);
            params = "name=" + URLEncoder.encode(service.get("Documentation Filename"), "UTF-8") + "&description=" + URLEncoder.encode(description, "UTF-8");

            final String binaryDocURL = "https://" + hostname + ":" + port + "/WSRR/8.5/Content/GenericDocument?" + params;

            // Load the requirements document for this service entry.
            //String requirementDocBsrUri = this.loadDocumentTree(binaryDocURL, requirementsFile);

            // Generate the master URL ready for POSTing REST XML to Service Registry.
            final String createURL = "https://" + hostname + ":" + port + "/WSRR/8.5/Content/GenericObject";
            System.out.println("--------------------------------------------------------------------------------");
            System.out.println("createURL is :" + createURL);
            System.out.println("--------------------------------------------------------------------------------");
//cs
            String sldBsrUri = this.createServiceLevelDefinition(createURL, service);
            sldBsrUri= this.createServiceLevelDefinitionXMLDataFuffa("SLD - ALFA_00 -","Rest","86eecc86-9f88-4880.b922.d76fe8d722b6","912fd491-3380-40e8.acb3.bf9a07bfb374");
            System.out.println(" sld " + sldBsrUri);
            //String serviceVersionBsrUri = this.createServiceVersion(createURL, service, wsdlDocBsrUri, sldBsrUri);
            

            /*
            @SuppressWarnings("rawtypes")
			ArrayList data=new ArrayList();
            
            //Business Service : SHOST SCHOST,SOPEN,SCOPEN
            
            data.add(0, "SHOST");
            data.add(1, "SHOST_Tool1");
 
            
            this.createBusinessServiceXMLData(data, "be5918be-68f4-441b.b0a3.25511e25a320");
            
            data.clear();
            data.add(0, "SCHOST");
            data.add(1, "SCHOST_Tool1");
            
            this.createBusinessServiceXMLData(data, "be5918be-68f4-441b.b0a3.25511e25a320");
            
            data.clear();
            data.add(0, "SOPEN");
            data.add(1, "SOPEN_Tool1");
            
            this.createBusinessServiceXMLData(data, "be5918be-68f4-441b.b0a3.25511e25a320");
            
            data.clear();
            data.add(0, "SCOPEN");
            data.add(1, "SCOPEN_Tool1");
            
            this.createBusinessServiceXMLData(data, "be5918be-68f4-441b.b0a3.25511e25a320");
 
 
            data.clear();
            data.add(0, "BC");
            data.add(1, "SHOST_Tool1");
            data.add(2, "ns");
            data.add(3, "00");  
            data.add(4, "pgm_servizio");
            data.add(5, "trans_servizio");
            data.add(6, "id_servizio");
            data.add(7, "pgm_md");
            data.add(8, "acronimo");
            data.add(9, "is_SSA");
            data.add(10, "descrizione");
            data.add(11, "descrizione est");
            data.add(12, "doc_analisi_funz");
            data.add(13, "doc_analisi_tecn");
            data.add(14, "data");
            data.add(15, "attivatoinprd");
            data.add(16, "pidprocesso");
            data.add(17, null);
            data.add(18, null);
            data.add(19, "11756111-20d1-41a0.b1b3.35b3e835b35a");
            data.add(20, "0e31fb0e-88c7-47ea.8d68.83cafc8368fd");
            
            
            //SHOSTServiceVersion
            this.createServiceSHOSTServiceVersionXMLDAta(data,"7b798f7b-60f4-4488.9f95.d6b84cd695ad");
            
            data.clear();
            
            data.add(0, "MPE");
            data.add(1, "SCHOST_Tool1");
            data.add(2, "ns");
            data.add(3, "00");  
            data.add(4, "pgm_servizio");
            data.add(5, "trans_servizio");
            data.add(6, "id_servizio");
            data.add(7, "pgm_md");
            data.add(8, "acronimo");
            data.add(9, "is_SSA");
            data.add(10, "descrizione");
            data.add(11, "descrizione est");
            data.add(12, "doc_analisi_funz");
            data.add(13, "doc_analisi_tecn");
            data.add(14, "data");
            data.add(15, "attivatoinprd");
            data.add(16, "pidprocesso");
            data.add(17, "11938c11-6744-44c5.b85c.6f1a9a6f5c60");
            data.add(18, "11938c11-6744-44c5.b85c.6f1a9a6f5c60");
            data.add(19, "11756111-20d1-41a0.b1b3.35b3e835b35a");
            data.add(20, "0e31fb0e-88c7-47ea.8d68.83cafc8368fd");
            
            //SCHOSTServiceVersion
            this.createServiceSCHOSTServiceVersionXMLDAta(data,"7b798f7b-60f4-4488.9f95.d6b84cd695ad");
            
 
            data.clear();
            
            data.add(0, "SCIIB");
            data.add(1, "SOPEN_Tool1");
            data.add(2, "ns");
            data.add(3, "00");  
            data.add(4, "acronimo");
            data.add(5, "is_SSA");
            data.add(6, "descrizione");
            data.add(7, "descrizione est");
            data.add(8, "doc_analisi_funz");
            data.add(9, "doc_analisi_tecn");
            data.add(10, "data");
            data.add(11, "attivatoinprd");
            data.add(12, "pidprocesso");
            
            //SOPENServiceVersion
            this.createServiceSOPENServiceVersionXMLDAta(data, "7b798f7b-60f4-4488.9f95.d6b84cd695ad");   
            
            
            data.clear();
            
            data.add(0, "WS"); //Rest
            data.add(1, "SCOPEN_Tool1");
            data.add(2, "ns");
            data.add(3, "00");  
            data.add(4, "acronimo");
            data.add(5, "is_SSA");
            data.add(6, "descrizione");
            data.add(7, "descrizione est");
            data.add(8, "doc_analisi_funz");
            data.add(9, "doc_analisi_tecn");
            data.add(10, "data");
            data.add(11, "attivatoinprd");
            data.add(12, "pidprocesso");
            
            //SCOPENServiceVersion
            this.createServiceSCOPENServiceVersionXMLDAta(data, "7b798f7b-60f4-4488.9f95.d6b84cd695ad");
            
            
            **/
 
        } // WHILE
    }

    /**
     * POSTs a document file to the specified query URL. If the file fails to load due to a dependent file needing to
     * load first, the method will recursively load all the dependants and try again.
     * 
     * @param queryURL
     *            Full path to the Service Registry POST URL including all the document properties
     * @param sourceFile
     *            The file of the document to load
     * @throws Exception
     */
    private String loadDocumentTree(String queryURL, File sourceFile) throws Exception {

        // Create the variable to return
        String bsrURI = null;

        // Attempt to load the document, but we may need to load any dependencies first.
        // If a document fails to load, the loadDocument method will throw a MustImportReferenceException.
        // This method will keep retrying until all the references have been loaded and the root document
        // can finally be loaded.
        boolean retry = true;

        // Keep retrying until we load the document or an unexpected exception is thrown
        while (retry) {
            try {
                // Attempt to load the root document
                bsrURI = this.loadDocument(queryURL, sourceFile);

                // The document loaded successfully, so no need to keep retrying
                retry = false;
            } catch (MustImportReferenceException reference) {
                // We cannot load the root document yet as there is a referenced file
                // that needs to be loaded first
                File referenceFile = new File(this.wsdlPath, reference.getFilename());
                String name = referenceFile.getName();

                // See what type of document we need to load, for example WSDL or XSD
                String extension = name.substring(name.lastIndexOf(".") + 1);
                String type = null;

                if (extension.equalsIgnoreCase("wsdl")) {
                    type = "WSDLDocument";
                } else if (extension.equalsIgnoreCase("xsd")) {
                    type = "XSDDocument";
                } else {
                    throw new Exception("Unsupported type " + extension + " when loading referenced file " + reference.getFilename());
                }

                // Load the referenced document using the loadDocumentTree so that recursive references can be loaded
                // also
                String referenceQueryURL = "http://" + this.hostname + ":" + this.port + "/WSRR/8.5/Content/" + type + "?name=" + URLEncoder.encode(name, "UTF-8");

                System.out.println("referenceQueryURL is :" + referenceQueryURL);
                System.out.println("referenceFile is :" + referenceFile);
                this.loadDocumentTree(referenceQueryURL, referenceFile);
            }
        } // WHILE

        return bsrURI;
    }

    /**
     * POSTs a document in to Service Registry
     * 
     * @param queryURL
     *            The full URL to POST the document to including all the document meta data as query parameters
     * @param sourceFile
     *            The file to POST
     * @throws MustImportReferenceException
     *             If the server throws an Error 500 with the codes "<code>GSR1350E</code><message>GSR0008E" then this
     *             exception is throws containing the filename of the document that must be loaded first.
     * @throws Exception
     */
    private String loadDocument(String queryURL, File sourceFile) throws Exception {
        // Create the variable to return
        String bsrURI = null;

        // Open a connection to Service Registry
        URL url = new URL(queryURL);

        System.out.println("url is :" + url);
        
       // String userPassword = "gabriele" + ":" + "viviana";
       // String encoding = new String(Base64.encodeBase64(userPassword
		//		.getBytes()));
        
        /**
         * 
         * 
         * 			url = new URL(expanded_url);

			HttpsURLConnection con = (HttpsURLConnection) url.openConnection();

			String userPassword = user + ":" + password;

			String encoding = new String(Base64.encodeBase64(userPassword
					.getBytes()));

			con.setRequestProperty("Authorization", "Basic " + encoding);

			con.setRequestMethod("PUT");

			con.connect();

         * 
         */

        HttpURLConnection urlConnection = (HttpURLConnection) url.openConnection();
        
        String userPassword = "gabriele" + ":" + "viviana";
        String encoding = new String(Base64.encodeBase64(userPassword
				.getBytes()));
        urlConnection.setRequestProperty("Authorization", "Basic " + encoding);
        urlConnection.setRequestMethod("POST");
        urlConnection.setRequestProperty("Content-Type", "UTF-8");
        urlConnection.setDoInput(true);
        urlConnection.setDoOutput(true);
        urlConnection.setUseCaches(false);

        // Read the file contents and send it to Service Registry
        InputStream in = new FileInputStream(sourceFile);
        OutputStream out = urlConnection.getOutputStream();

        int c;
        while ((c = in.read()) != -1) {
            out.write(c);
        }
        out.flush();

        // Read the response from the server
        BufferedReader reader = null;
        try {
            System.out.println("+++++++ ");

            // Check for a successful POST and the document has been created
            InputStream inputStream = urlConnection.getInputStream();
            if (urlConnection.getResponseCode() == 201) // Created
            {
                bsrURI = processResponse(inputStream);
                System.out.println("Successfully created " + sourceFile.getName());
            } else {
                reader = new BufferedReader(new InputStreamReader(urlConnection.getInputStream()));
                StringBuffer stringBuffer = new StringBuffer();
                String line = null;
                while (null != (line = reader.readLine())) {
                    stringBuffer.append(line);
                }
                reader.close();
                throw new Exception("Unable to create " + sourceFile.getName() + ": " + stringBuffer.toString());
            }
        } catch (IOException ex) {
            // If we fail to read the response, check the error stream as this may include details
            // of the required dependency that we need to handle

            // Attempt to read the error stream
            System.out.println("------------------------");
            System.out.println("------------------------");
            System.out.println("ex is-----" + ex.toString());
            System.out.println("------------------------");
            System.out.println("------------------------");
            reader = new BufferedReader(new InputStreamReader(urlConnection.getErrorStream()));
            StringBuffer stringBuffer = new StringBuffer();
            String line = null;

            while (null != (line = reader.readLine())) {
                stringBuffer.append(line);
            }
            reader.close();

            if (urlConnection.getResponseCode() == 500) {
                // We have an error 500 exception, attempt to see if it is a GSR0008E exception indicating
                // that we must import a dependency first.
                String referencedFile = getReferencedFilename(stringBuffer.toString());

                // If the referenced file is null, it was a different error, so re-throw it, otherwise,
                // prepare a MustImportReferenceException so the dependency can be handled
                if (referencedFile != null) {
                    throw new MustImportReferenceException(referencedFile);
                }
            }

            // Unknown cause of error, throw an exception with the details
            throw new Exception("Received unexpected resposne " + urlConnection.getResponseCode() + ": " + stringBuffer.toString());
        }

        return bsrURI;
    }

    /**
     * Check the response string for an instance of GSR1350E/GSR0008E that indicates a dependency must be loaded. Also
     * extract the filename of the dependency and return it.
     * 
     * @param responseError
     *            The response message from the server
     * @return The filename of the dependency file if the message matched, otherwise return null if the cause was
     *         something different.
     */
    private String getReferencedFilename(String responseError) {
        // Create a regular expression to extract the name of the file matching the correct error codes.
        // The filename will be contained within HTML encoded quote characters.
        String regEx = "<code>GSR1350E</code><message>GSR0008E:.+&quot;((.+))&quot;";

        Pattern p = Pattern.compile(regEx);
        Matcher m = p.matcher(responseError);

        // Find the name of the referenced file
        if (m.find()) {
            if (m.groupCount() == 2) {
                return m.group(1); // Name is second match in group
            }
        }

        // Return null if there is no match on a reference import
        return null;
    }

  

    public String createBusinessServiceXMLData(TWList data, String serviceVersionBsrUri,String organizationBsrUri) {

        String output=null;
        
 
        String type=(String) data.getArrayData(1);
        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }
        	
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();
            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState ale63_assetType
             * ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(2)));
            
            //propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, (String) data.get(4)));
            
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_ISP_SERVICE+type+"Service"));
                     
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_WEB_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_FULL_DESCRIPTION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REMOTE_STATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_TYPE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REQUIREMENTS_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_OWNER_EMAIL, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_GUID, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_COMMUNITY_NAME, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_OWNERS, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_serviceInterfaceVersions gep63_charter
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_DEPENDENCY, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_ARTIFACTS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_OWNING_ORGANIZATION, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_SERVICE_INTERFACE_VERSIONS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CHARTER, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CAPABILITY_VERSIONS, serviceVersionBsrUri));
            //
            if ( organizationBsrUri != null && !organizationBsrUri.equals("nf")){
            relationshipsElement.appendChild(createRelationshipElement(document, "ale63_owningOrganization", organizationBsrUri));
            }
            
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
            /*
             * Process the HTTP response.
             */

        } catch (Exception e) {
            e.printStackTrace();
            output=e.getMessage();
        }
        System.out.println((String) data.getArrayData(0) +".............................................................................");
        System.out.println(output);
        System.out.println(".................................................................................................");
        return output;
    }

 /////////////////////////////////////////REST INTERFACE////////////////////////////////////////////////////////////////////////   
 //aggiungere documenti collegati  public String createRestInterfaceXMLData(String name,TWList data)
 ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // public String createRestInterfaceXMLData(String name) {
      public String createRestInterfaceXMLData(String name,TWList data) {
        String output=null;

        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }

            Document document = docBuilder.newDocument();

            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE,""));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, ""));
            
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_REST_INTERFACE));
                       
            propertiesElement.appendChild(createPropertyElement(document, "sm63_interfaceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_interfaceVersion", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_interfaceNamespace","X"));
            propertiesElement.appendChild(createPropertyElement(document, "rest80_webLink", EMPTY_STRING));
            
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);
 
            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_wsdlPortTypes", null));
            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_schemaDependencies", null));
            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_operations", null));
            //relationshipsElement.appendChild(createRelationshipElement(document, "rest80_definitionDocument", null)); 
            
            boolean definitiondocument=false;
                 	
        		int size = data.getArraySize();
        		for (int i = 0; i < size; i++) {
        			String bsrURIDocument = (String) data.getArrayData(i);
        			if (bsrURIDocument.length() !=0 ) {
        			   relationshipsElement.appendChild(createRelationToDocument(document,"rest80_definitionDocument",bsrURIDocument,"GenericDocument"));
        			   definitiondocument=true;
        			}       		
        		}
        		
        		
            if (!definitiondocument) {
            	relationshipsElement.appendChild(createRelationshipElement(document, "rest80_definitionDocument", null));
            }
            	
            
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
 
        } catch (Exception e) {
            e.printStackTrace();
            output=e.getMessage();
        }
        return output;
    }
    
    
    //281117 aggiungo alla fine dei parametri anche la versione.
    public  String createServiceSCOPENServiceVersionXMLDAta(TWList data,String sdlBsrUri,String organizationBsrUri,String matricola,String version) {
    	
 
        String output=null;

        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name namespace version description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState
             * ale63_assetType ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             * gep63_consumerIdentifier gep63_versionAvailabilityDate gep63_versionTerminationDate
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(2)));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE,""));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION, version)); //281117
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,(String) data.getArrayData(5)));

            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ACRONIMO", (String) data.getArrayData(3))); 
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", (String) data.getArrayData(4)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DESC_ESTESA", (String) data.getArrayData(6))); 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_FUNZIONALE", (String) data.getArrayData(7)));                       
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_TECNICA",(String) data.getArrayData(8)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_ULTIMO_UTILIZZO", (String) data.getArrayData(9)));                  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_PROD", (String) data.getArrayData(10)));           
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PID_PROCESSO_GOV", (String) data.getArrayData(11))); 
            
           	//aggiunta 05102016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ABILITAZ_INFRASTR", (String) data.getArrayData(12)));
            
            //17122016 reps0 fields
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA", (String)data.getArrayData(13)));
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_FLG_CTRL_TIPOLOGIA", (String)data.getArrayData(14)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_UTILIZ_PIU_BAN_CLONI", (String)data.getArrayData(15)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DISP_SERV", (String)data.getArrayData(16)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_VINCOLI_RIUSO", (String)data.getArrayData(17)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_INFO_COSTO", (String)data.getArrayData(18)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PIATT_EROG", (String)data.getArrayData(19)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_RITIRO_SERV", (String)data.getArrayData(20)));
                       
            //201216 +
            //040117 -
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_USO_SICUREZZA", (String)data.getArrayData(21)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_EAR_SERVIZIO", (String)data.getArrayData(21)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_AMBITO_IMPLEMENTAZIONE", (String)data.getArrayData(22)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_LINK_SIN_APPS_EST", (String)data.getArrayData(23)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_AMBIENTE_FISICO", (String)data.getArrayData(24)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_REPS0", (String)data.getArrayData(25)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_RIF_CHIAMANTI_EST", (String)data.getArrayData(26)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_RIF_CHIAMANTI_INT", (String)data.getArrayData(27)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_DOWNTIME_PIANIFICATO", (String)data.getArrayData(28)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_STATO_ATTUALE_FUNZ", (String)data.getArrayData(29)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_DIM_MAX_MSG", (String)data.getArrayData(30)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_DIM_MIN_MSG", (String)data.getArrayData(31)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_VOLUME_GIORN", (String)data.getArrayData(32)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_NUM_CHIAMATE_PICCO", (String)data.getArrayData(33)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_FLG_CONTIENE_ATTACHMENT", (String)data.getArrayData(34)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCOPEN_ATTACHMENT_TYPE", (String)data.getArrayData(35)));
            
            //08032017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_DETTAGLIO", (String)data.getArrayData(36)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SECURITY_ROLE", (String)data.getArrayData(37)));
            
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_APPL", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_SYST", EMPTY_STRING));
                       
            //17122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_PUBBL_CREAZ_SERV", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_PUBBLICATORE_CREAZ_SERV", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_MODIFICA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_CREAZIONE", matricola));
            
            //230217
            /**
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", ""));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ESPOSTO_COME_API", ""));
            **/
            
            //31032017 i campi ora arrivano in input gep63_DERIVANTE_DA_ALTRI_SERV - gep63_TIPOLOGIA_OGGETTO_ESISTENTE - gep63_NOME_SERVIZIO_PRECEDENTE 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", (String)data.getArrayData(38)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", (String)data.getArrayData(39)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", (String)data.getArrayData(40)));
            
            //costruisco il primary type dell'oggetto
                       
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_ISP_SERVICE_VERSION+"SCOPENServiceVersion"));
            
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_WEB_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_FULL_DESCRIPTION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REMOTE_STATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_TYPE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REQUIREMENTS_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_OWNER_EMAIL, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_GUID, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_COMMUNITY_NAME, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_OWNERS, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_AVAILABILITY_DATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_TERMINATION_DATE, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_consumes gep63_provides
             * gep63_interfaceSpecifications gep63_providedWebServices gep63_providedRESTServices
             * gep63_providedSCAModules
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_DEPENDENCY, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_ARTIFACTS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_OWNING_ORGANIZATION,organizationBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CONSUMES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDES, sdlBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_INTERFACE_SPECIFICATIONS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_SCA_MODULES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_WEB_SERVICES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_REST_SERVICES, null));
   
            // Classifications element
            String classificazione=(String) data.getArrayData(0);
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(classificationsElement.appendChild(createClassificationElement(document,"http://isp/#"+classificazione)));

            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
 
        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }
        System.out.println("SCOPENServiceVersion.............................................................................");
        System.out.println(output);
        System.out.println(".................................................................................................");

        return output;
    }
    //281117 aggiungo alla fine dei parametri anche la versione.
    public  String createServiceSHOSTServiceVersionXMLDAta( TWList data,String sdlBsrUri,String organizationBsrUri,String matricola,String version) {
 
    	
        String output=null;
        String type =(String) data.getArrayData(0);

        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name namespace version description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState
             * ale63_assetType ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             * gep63_consumerIdentifier gep63_versionAvailabilityDate gep63_versionTerminationDate
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(2)));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, ""));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION, version)); //281117
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, (String) data.getArrayData(9)));
            
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_SERVIZIO", (String) data.getArrayData(3)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_TRANS_SERVIZIO", (String) data.getArrayData(4)));         
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_ID_SERVIZIO", (String) data.getArrayData(5)));           
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_MD", (String) data.getArrayData(6)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_CONVNULL", (String)data.getArrayData(7)));
            
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ACRONIMO", (String) data.getArrayData(7))); 
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", (String) data.getArrayData(8)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DESC_ESTESA",(String) data.getArrayData(10))); 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_FUNZIONALE", (String) data.getArrayData(11)));                       
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_TECNICA", (String) data.getArrayData(12)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_ULTIMO_UTILIZZO", (String) data.getArrayData(13)));                  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_PROD", (String) data.getArrayData(14)));           
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PID_PROCESSO_GOV", (String) data.getArrayData(15)));  
                       
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_APPL", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_SYST", EMPTY_STRING));
            
            //17122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_PUBBL_CREAZ_SERV", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_PUBBLICATORE_CREAZ_SERV", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_MODIFICA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_CREAZIONE", matricola));
            
            //01122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_MD_X_MPE",(String) data.getArrayData(23)));
            
            //17122016 reps0 fields
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA", (String)data.getArrayData(24)));
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_FLG_CTRL_TIPOLOGIA", (String)data.getArrayData(25)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_UTILIZ_PIU_BAN_CLONI", (String)data.getArrayData(26)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DISP_SERV", (String)data.getArrayData(27)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_VINCOLI_RIUSO", (String)data.getArrayData(28)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_INFO_COSTO", (String)data.getArrayData(29)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PIATT_EROG", (String)data.getArrayData(30)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_RITIRO_SERV", (String)data.getArrayData(31)));
            //040117 -
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_USO_SICUREZZA", (String)data.getArrayData(32)));
            
            //08032017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_DETTAGLIO", (String)data.getArrayData(32)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SECURITY_ROLE", (String)data.getArrayData(33)));
            
            //230217
            /**
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", ""));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ESPOSTO_COME_API", ""));
            **/
            
            //31032017 i campi ora arrivano in input gep63_DERIVANTE_DA_ALTRI_SERV - gep63_TIPOLOGIA_OGGETTO_ESISTENTE - gep63_NOME_SERVIZIO_PRECEDENTE 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", (String)data.getArrayData(34)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", (String)data.getArrayData(35)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", (String)data.getArrayData(36)));
           
            //12052017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_PGM_MD_X_INTEROPER", ""));
            
            //costruisco il primary type dell'oggetto
            
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_ISP_SERVICE_VERSION+"SHOSTServiceVersion"));
            
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_WEB_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_FULL_DESCRIPTION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REMOTE_STATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_TYPE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REQUIREMENTS_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_OWNER_EMAIL, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_GUID, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_COMMUNITY_NAME, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_OWNERS, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_AVAILABILITY_DATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_TERMINATION_DATE, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_consumes gep63_provides
             * gep63_interfaceSpecifications gep63_providedWebServices gep63_providedRESTServices
             * gep63_providedSCAModules
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_DEPENDENCY, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_ARTIFACTS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_OWNING_ORGANIZATION, organizationBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CONSUMES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDES, sdlBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_INTERFACE_SPECIFICATIONS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_SCA_MODULES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_WEB_SERVICES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_REST_SERVICES, null));
            
            /*
             * aggiungo le relazioni per copycobol Obbligatorie ed eventualmente i due xsd (opzionali)
             * 
             */
    
            	
            	String now=(String) data.getArrayData(16); //xsddfdlinput
            	if (now != "") {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_DFDL_INP",now,"XSDDocument"));      		
            	} else {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_DFDL_INP",null,null));
            	}
            	now=(String) data.getArrayData(17); //xsddfdloutput
               	if (now != "") { 
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_DFDL_OUT",now,"XSDDocument"));    		
            	}else {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_DFDL_OUT",null,null));
            	}
               	
               	//copy cobol sono obbligatori e di tipo GenericDocument (deprecato)
               	
            	now=(String) data.getArrayData(18); //cpycobolInp
            	if (now != "") {
            		//relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_CPY_INP",now,"GenericDocument")); //fix type assumo Generic Document     		
            	}
            	now=(String) data.getArrayData(19); //cpycobolOut (deprecato)
               	if (now != "") { 
            		//relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SHOST_CPY_OUT",now,"GenericDocument")); //fix type assumo Generic Document    		
            	}
               	
                //26/07/2016 
               	now=(String)data.getArrayData(20);
               	if (now != "") 
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_NOME_CPY_INP", now));
               	 else
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_NOME_CPY_INP", EMPTY_STRING));
               	
               	now=(String)data.getArrayData(21);
               	if (now != "") 
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_NOME_CPY_OUT", now));
               	 else
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SHOST_NOME_CPY_OUT", EMPTY_STRING));
  
               	//aggiunta 05102016
               	now=(String)data.getArrayData(22);
               	propertiesElement.appendChild(createPropertyElement(document, "gep63_ABILITAZ_INFRASTR", now));
               	
               	
            // Classifications element
            String classificazione=(String) data.getArrayData(0);
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(classificationsElement.appendChild(createClassificationElement(document,"http://isp/#"+classificazione)));

            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
 
        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }
        System.out.println("SHOSTServiceVersion.............................................................................");
        System.out.println(output);
        System.out.println(".................................................................................................");
        return output;
    }
    //17012018 passo anche a questo metodo la versione in modo che sia allineato con gli altri
    //inoltre la versione non viene piu' settata del codice:
    /*
     *      String versione_corrente="00";            
            if (((String)data.getArrayData(0)).equals("BSNBP")) {
            	versione_corrente=(String) data.getArrayData(5);
            }          
            if (((String)data.getArrayData(0)).equals("MPE")) {
            	versione_corrente=(String) data.getArrayData(5);
            }
     */
    //ma viene presa quella passata
    public String createServiceSCHOSTServiceVersionXMLDAta(TWList data,String sdlBsrUri,String organizationBsrUri,String matricola,String versione) {
   	
        String output=null;
        String type =(String) data.getArrayData(0);

        try {
        	
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                output=e.getMessage();
                throw e;
               
            }
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name namespace version description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState
             * ale63_assetType ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             * gep63_consumerIdentifier gep63_versionAvailabilityDate gep63_versionTerminationDate
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(2)));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, ""));
                        
            String versione_corrente=versione;
            /**    deprecata
            //02022017 se BS o MPE la versione viene presa dal campo a video: tipo interfaccia
        
            String versione_corrente="00";            
            if (((String)data.getArrayData(0)).equals("BSNBP")) {
            	versione_corrente=(String) data.getArrayData(5);
            }          
            if (((String)data.getArrayData(0)).equals("MPE")) {
            	versione_corrente=(String) data.getArrayData(5);
            }
            **/
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION, versione));//170118
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, (String) data.getArrayData(9)));
            
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_TRANS_SERVIZIO", (String) data.getArrayData(3)));         
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_ID_SERVIZIO", (String) data.getArrayData(4)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_COD_VERSIONE", (String) data.getArrayData(5)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_MD", (String)data.getArrayData(6)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_CONVNULL", (String)data.getArrayData(7)));
            
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ACRONIMO", (String)data.getArrayData(7))); 
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", (String)data.getArrayData(8)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DESC_ESTESA",(String) data.getArrayData(10))); 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_FUNZIONALE", (String)data.getArrayData(11)));                       
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_TECNICA", (String)data.getArrayData(12)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_ULTIMO_UTILIZZO",(String)data.getArrayData(13)));                  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_PROD", (String)data.getArrayData(14)));           
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PID_PROCESSO_GOV", (String)data.getArrayData(15)));  
            
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_APPL", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_SYST", EMPTY_STRING)); 
            
            //17122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_PUBBL_CREAZ_SERV", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_PUBBLICATORE_CREAZ_SERV", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_MODIFICA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_CREAZIONE", matricola));
            
            //01122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_MD_X_MPE",(String) data.getArrayData(23)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_SERVIZIO",(String) data.getArrayData(24)));
            
            //17122016 reps0 fields
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA", (String)data.getArrayData(25)));
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_FLG_CTRL_TIPOLOGIA", (String)data.getArrayData(26)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_UTILIZ_PIU_BAN_CLONI", (String)data.getArrayData(27)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DISP_SERV", (String)data.getArrayData(28)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_VINCOLI_RIUSO", (String)data.getArrayData(29)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_INFO_COSTO", (String)data.getArrayData(30)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PIATT_EROG", (String)data.getArrayData(31)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_RITIRO_SERV", (String)data.getArrayData(32)));
            //040117 -
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_USO_SICUREZZA", (String)data.getArrayData(33)));
            
            //08032017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_DETTAGLIO", (String)data.getArrayData(33)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SECURITY_ROLE", (String)data.getArrayData(34)));
            
            //230217
            /**
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", ""));
            **/
            
            //31032017 i campi ora arrivano in input gep63_DERIVANTE_DA_ALTRI_SERV - gep63_TIPOLOGIA_OGGETTO_ESISTENTE - gep63_NOME_SERVIZIO_PRECEDENTE 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", (String)data.getArrayData(35)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", (String)data.getArrayData(36)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", (String)data.getArrayData(37)));
            
            //10052017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_PGM_MD_X_INTEROPER", ""));
            
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ESPOSTO_COME_API", ""));
                  
            //costruisco il primary type dell'oggetto  
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_ISP_SERVICE_VERSION+"SCHOSTServiceVersion"));
            
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_WEB_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_FULL_DESCRIPTION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REMOTE_STATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_TYPE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REQUIREMENTS_LINK, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_OWNER_EMAIL, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_GUID, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_COMMUNITY_NAME, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_OWNERS, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_AVAILABILITY_DATE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_TERMINATION_DATE, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_consumes gep63_provides
             * gep63_interfaceSpecifications gep63_providedWebServices gep63_providedRESTServices
             * gep63_providedSCAModules
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_DEPENDENCY, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_ARTIFACTS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_OWNING_ORGANIZATION, organizationBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CONSUMES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDES, sdlBsrUri));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_INTERFACE_SPECIFICATIONS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_SCA_MODULES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_WEB_SERVICES, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_REST_SERVICES, null));
            
            /*
             * aggiungo le relazioni per copycobol Obbligatorie ed eventualmente i due xsd (opzionali)
             * 
             */
    
            	
            	String now=(String)data.getArrayData(16); //xsddfdlinput
            	if (now != "") {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_DFDL_INP",now,"XSDDocument"));      		
            	} else {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_DFDL_INP",null,null));
            	}
            	now=(String)data.getArrayData(17); //xsddfdloutput
               	if (now != "") { 
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_DFDL_OUT",now,"XSDDocument"));    		
            	}else {
            		relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_DFDL_OUT",null,null));
            	}
               	
               	//copy cobol sono obbligatori e di tipo GenericDocument 
               	
            	now=(String)data.getArrayData(18);//cpycobolInp
            	if (now != "") {
            		//relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_CPY_INP",now,"GenericDocument")); //fix type assumo Generic Document     		
            	}
            	now=(String)data.getArrayData(19); //cpycobolOut
               	if (now != "") { 
            		//relationshipsElement.appendChild(createRelationToDocument(document,"gep63_SCHOST_CPY_OUT",now,"GenericDocument")); //fix type assumo Generic Document    		
            	}
               	
                //26/07/2016 
               	now=(String)data.getArrayData(20);
               	if (now != "") 
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_NOME_CPY_INP", now));
               	 else
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_NOME_CPY_INP", EMPTY_STRING));
               	
               	now=(String)data.getArrayData(21);
               	if (now != "") 
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_NOME_CPY_OUT", now));
               	 else
               		propertiesElement.appendChild(createPropertyElement(document, "gep63_SCHOST_NOME_CPY_OUT", EMPTY_STRING));
               	
               	//aggiunta 05102016
               	now=(String)data.getArrayData(22);
               	propertiesElement.appendChild(createPropertyElement(document, "gep63_ABILITAZ_INFRASTR", now));
   
            // Classifications element
            String classificazione=(String)data.getArrayData(0);
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(classificationsElement.appendChild(createClassificationElement(document,"http://isp/#"+classificazione)));

            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
 
        } catch (Exception e) {
            e.printStackTrace();
            output=e.getMessage();
        }
        System.out.println("SCHOSTServiceVersion.............................................................................");
        System.out.println(output);
        System.out.println(".................................................................................................");
        return output;
    }

    private String createServiceLevelDefinition(String createURL, HashMap<String, String> service) {

        // Create the variable to return
        String bsrURI = null;

        try {
            /*
             * First, create the HTTP connection to the WSRR instance and configure it with the right request method and
             * content type.
             */
            URL url = new URL(createURL);
            HttpURLConnection urlConnection = (HttpURLConnection) url.openConnection();
            urlConnection.setRequestMethod("POST");
            urlConnection.setRequestProperty("Content-Type", "text/xml; charset=UTF-8");
            urlConnection.setDoInput(true);
            urlConnection.setDoOutput(true);
            urlConnection.setUseCaches(false);

            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name description gep63_consumerIdentifierLocationInfo gep63_contextIdentifierLocationInfo
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, SLD_NAME_PREFIX + service.get("Name")));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_SLD));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER_LOCATION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONTEXT_IDENTIFIER_LOCATION, EMPTY_STRING));

            Object[] inserts = new Object[] { service.get("Version"), service.get("Name") };
            String description = MessageFormat.format(SLD_DESCRIPTION, inserts);
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, description));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * gep63_boundScaExport gep63_anonymousSLA gep63_compatibleSLDs gep63_boundWebServicePort
             * gep63_boundRESTService gep63_serviceInterface gep63_availableEndpoints gep63_availableOperations
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_SCA_EXPORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_ANONYMOUS_SLA, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CAMPATIBLE_SLDS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_WEB_SERVICE_PORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_REST_SERVICE, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_SERVICE_INTERFACE, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_AVAILABLE_ENDPOINTS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_AVAILABLE_OPERATIONS, null));

            // Classifications element
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);

            /*
             * Write the XML document to the output stream of the HTTP connection.
             */
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            DOMSource source = new DOMSource(document);
            StreamResult result = new StreamResult(urlConnection.getOutputStream());
            transformer.transform(source, result);

            /*
             * Process the HTTP response.
             */
            System.out.println("+++++++ ");

            // Check for a successful POST and the document has been created
            InputStream inputStream = urlConnection.getInputStream();
            if (urlConnection.getResponseCode() == 201) // Created
            {
                bsrURI = processResponse(inputStream);
                System.out.println("Successfully created Service Level Definition: " + service.get("Name") + " (" + bsrURI + ")");
            } else {
                BufferedReader reader = new BufferedReader(new InputStreamReader(urlConnection.getInputStream()));
                StringBuffer stringBuffer = new StringBuffer();
                String line = null;
                while (null != (line = reader.readLine())) {
                    stringBuffer.append(line);
                }
                reader.close();

                throw new Exception("Unable to create Service Level Definition: " + service.get("Name") + ": " + stringBuffer.toString());
            }

            urlConnection.disconnect();
        } catch (Exception e) {
            e.printStackTrace();
        }

        return bsrURI;
    }

    private Element createPropertyElement(Document document, String name, String value) {
        Element element = document.createElement(ELEMENT_PROPERTY);
        element.setAttribute(ATTR_NAME, name);
        element.setAttribute(ATTR_VALUE, value);
        return element;
    }

    private Element createClassificationElement(Document document, String classification) {
        Element element = document.createElement(ELEMENT_CLASSIFICATION);
        element.setAttribute(ATTR_URI, classification);
        return element;
    }
    
    private Element createRelationshipElement(Document document, String name, String targetBsrUri) {
        Element element = document.createElement(ELEMENT_RELATIONSHIP);
        element.setAttribute(ATTR_NAME, name);
        if (targetBsrUri != null) {
            element.setAttribute(ATTR_TARGET_BSRURI, targetBsrUri);
        }
        return element;
    }
    
    private Element createRelationshipElementServiceInterface(Document document, String targetBsrUri) {
        Element element = document.createElement(ELEMENT_RELATIONSHIP);
        element.setAttribute(ATTR_NAME, "gep63_serviceInterface");
        if (targetBsrUri != null) {
            element.setAttribute(ATTR_TARGET_BSRURI, targetBsrUri);
        }
        element.setAttribute(ATTR_TARGET_TYPE, "GenericObject");
        element.setAttribute(ATTR_PRIMARY_TYPE, OWL_REST_INTERFACE);
        return element;
    }
    
    private Element createRelationshipElementEndpoint(Document document,String interfacetype, String targetBsrUri) {
        Element element = document.createElement(ELEMENT_RELATIONSHIP);
        element.setAttribute(ATTR_NAME, "gep63_availableEndpoints");
        if (targetBsrUri != null) {
            element.setAttribute(ATTR_TARGET_BSRURI, targetBsrUri);
        }
        String type="";
        if (interfacetype == null) interfacetype="REST"; 
        
        switch (interfacetype) {
        case "REST": type=OWL_REST_ENDPOINT;
                     break;
        case "SOAP": type=OWL_SOAP_ENDPOINT;
                     break;
        case "CICS": type=OWL_CICS_ENDPOINT;
                     break;
        case "MQ":   type=OWL_MQ_ENDPOINT;
                     break;
        case "CALLABLE":   type=OWL_CALLABLE_ENDPOINT;
        			 break;            
                     
        default:     type=OWL_REST_ENDPOINT;
                     break;       
        }      
        element.setAttribute(ATTR_TARGET_TYPE, "GenericObject");
        element.setAttribute(ATTR_PRIMARY_TYPE, type);
        return element;
    }
    
    private Element createRelationToDocument(Document document,String name,String targetBsrURI, String targetDocumentType ){
    	
    	Element element = document.createElement(ELEMENT_RELATIONSHIP);
    	element.setAttribute(ATTR_NAME, name);
    	if (targetBsrURI != null) {
    		element.setAttribute(ATTR_TARGET_BSRURI, targetBsrURI);
    	}
    	if (targetDocumentType !=null ){
    		element.setAttribute(ATTR_TARGET_TYPE, targetDocumentType);
    	}
    	
    	return element;
    }

    private String processResponse(InputStream inputStream) throws Exception {

        // Create the variable to return
        String value = null;

        try {
            Document doc = docBuilder.parse(inputStream);
            value = (String) valueAttrExpression.evaluate(doc, XPathConstants.STRING);
        } catch (IOException e) {
            e.printStackTrace();
            throw e;
        } catch (SAXException e) {
            e.printStackTrace();
            throw e;
        } catch (XPathExpressionException e) {
            e.printStackTrace();
            throw e;
        }

        return value;
    }
    
	public String getItems(TWList items) {
		StringBuffer buffer = new StringBuffer();
		int size = items.getArraySize();
		for (int i = 0; i < size; i++) {
			String member = (String) items.getArrayData(i);
			buffer.append(member);
			if (i < (size - 1)) {
				buffer.append(',');
			}
		}
		return buffer.toString();
	}
	
	public String getItemsWSRR(TWList items,int indice) {
		return (String) items.getArrayData(indice);
	}
    //281117 aggiungo alla fine dei parametri anche la versione.
	public String createServiceSOPENServiceVersionXMLDAta(TWList data,String sdlBsrUri,String organizationBsrUri,String matricola,String version) {
	
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }
	        /*
	         * Now create the XML document that represents the BusinessService
	         */
	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);
	
	        /*
	         * Create elements for each of the required properties on the BusinessService type, as follows:
	         * 
	         * name namespace version description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState
	         * ale63_assetType ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
	         * gep63_consumerIdentifier gep63_versionAvailabilityDate gep63_versionTerminationDate
	         */
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(2)));
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE,""));
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION, version));//281117
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, (String) data.getArrayData(5)));
	
	        //propertiesElement.appendChild(createPropertyElement(document, "gep63_ACRONIMO", (String) data.getArrayData(3))); 
	        //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", (String) data.getArrayData(4)));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ID_SSA", EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, "gep63_DESC_ESTESA",(String) data.getArrayData(6))); 
	        propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_FUNZIONALE", (String) data.getArrayData(7)));                       
	        propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_TECNICA", (String) data.getArrayData(8)));
	        //propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_ULTIMO_UTILIZZO", (String) data.getArrayData(9)));                  
	        propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_PROD", (String) data.getArrayData(10)));           
	        propertiesElement.appendChild(createPropertyElement(document, "gep63_PID_PROCESSO_GOV", (String) data.getArrayData(11))); 
	        
           	//aggiunta 05102016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ABILITAZ_INFRASTR", (String) data.getArrayData(12)));
            
            //17122016 reps0 fields
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA", (String)data.getArrayData(13)));
            //110117
            propertiesElement.appendChild(createPropertyElement(document, "gep63_FLG_CTRL_TIPOLOGIA", (String)data.getArrayData(14)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_UTILIZ_PIU_BAN_CLONI", (String)data.getArrayData(15)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DISP_SERV", (String)data.getArrayData(16)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_VINCOLI_RIUSO", (String)data.getArrayData(17)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_INFO_COSTO", (String)data.getArrayData(18)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_PIATT_EROG", (String)data.getArrayData(19)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_RITIRO_SERV", (String)data.getArrayData(20)));	        
            
            //201216 + 
            //040116 -
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_USO_SICUREZZA", (String)data.getArrayData(21)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_EAR_SERVIZIO", (String)data.getArrayData(21)));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_AMBITO_IMPLEMENTAZIONE", (String)data.getArrayData(22)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_LINK_SIN_APPS_EST", (String)data.getArrayData(23)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_AMBIENTE_FISICO", (String)data.getArrayData(24)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_REPS0", (String)data.getArrayData(25)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_RIF_CHIAMANTI_EST", (String)data.getArrayData(26)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_RIF_CHIAMANTI_INT", (String)data.getArrayData(27)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_DOWNTIME_PIANIFICATO", (String)data.getArrayData(28)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_STATO_ATTUALE_FUNZ", (String)data.getArrayData(29)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_DIM_MAX_MSG", (String)data.getArrayData(30)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_DIM_MIN_MSG", (String)data.getArrayData(31)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_VOLUME_GIORN", (String)data.getArrayData(32)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_NUM_CHIAMATE_PICCO", (String)data.getArrayData(33)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_FLG_CONTIENE_ATTACHMENT", (String)data.getArrayData(34)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_ATTACHMENT_TYPE", (String)data.getArrayData(35)));  
            
            //08032017
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DOC_ANALISI_DETTAGLIO", (String)data.getArrayData(36)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SECURITY_ROLE", (String)data.getArrayData(37)));
            
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_APPL", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_ATTIVATO_IN_SYST", EMPTY_STRING));
            
            //17122016
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DATA_PUBBL_CREAZ_SERV", EMPTY_STRING));  
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_PUBBLICATORE_CREAZ_SERV", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_MODIFICA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_MATR_RICH_CREAZIONE", matricola));
            
            //230217
            /**
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", ""));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", ""));
            //propertiesElement.appendChild(createPropertyElement(document, "gep63_ESPOSTO_COME_API", ""));
            **/
            
            //31032017 i campi ora arrivano in input gep63_DERIVANTE_DA_ALTRI_SERV - gep63_TIPOLOGIA_OGGETTO_ESISTENTE - gep63_NOME_SERVIZIO_PRECEDENTE 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_DERIVANTE_DA_ALTRI_SERV", (String)data.getArrayData(38)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_TIPOLOGIA_OGGETTO_ESISTENTE", (String)data.getArrayData(39)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_NOME_SERVIZIO_PRECEDENTE", (String)data.getArrayData(40)));

            //230118 
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_ABILITAZ_READ", (String)data.getArrayData(41)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_ABILITAZ_WRITE", (String)data.getArrayData(42)));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_SOPEN_MOD_UTENTI_BUS", (String)data.getArrayData(43)));
            
            
	       //costruisco il primary type dell'oggetto	        	        
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_ISP_SERVICE_VERSION+"SOPENServiceVersion"));
	        
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_WEB_LINK, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_FULL_DESCRIPTION, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REMOTE_STATE, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_TYPE, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_REQUIREMENTS_LINK, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_OWNER_EMAIL, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_GUID, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_COMMUNITY_NAME, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_ASSET_OWNERS, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER,EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_AVAILABILITY_DATE, EMPTY_STRING));
	        propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_VERSION_TERMINATION_DATE, EMPTY_STRING));
	
	        // Relationships element
	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);
	
	        /*
	         * Create elements for each of the required relationships on the BusinessService type, as follows:
	         * 
	         * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_consumes gep63_provides
	         * gep63_interfaceSpecifications gep63_providedWebServices gep63_providedRESTServices
	         * gep63_providedSCAModules
	         */
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_DEPENDENCY, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_ARTIFACTS, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_ALE63_OWNING_ORGANIZATION, organizationBsrUri));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CONSUMES, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDES, sdlBsrUri));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_INTERFACE_SPECIFICATIONS, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_SCA_MODULES, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_WEB_SERVICES, null));
	        relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_PROVIDED_REST_SERVICES, null));
	
	        // Classifications element
	        String classificazione=(String) data.getArrayData(0);
	        Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
	        resourceElement.appendChild(classificationsElement);
	        classificationsElement.appendChild(classificationsElement.appendChild(createClassificationElement(document,"http://isp/#"+classificazione)));
	
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    System.out.println("SOPENServiceVersion.............................................................................");
	    System.out.println(output);
	    System.out.println(".................................................................................................");
	    return output;
	}
	
	//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
	//08032017 aggiungo il campo sm63_ESPOSTO_COME_API
	public String createRestEndpointXMLDAta(String name,String timeout,String environment,String state,String bsrUriserviceProxy,String sicurezza,String espostoComeApi) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "rest80_baseURL", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","REST"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", "X"));
            
            
            //040117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            
            
            propertiesElement.appendChild(createPropertyElement(document, "rest80_ISPHEADER_FLAG", null));
            
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            
            //08032017
            propertiesElement.appendChild(createPropertyElement(document, "rest80_ESPOSTO_COME_API", espostoComeApi));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_REST_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	        
            if ( bsrUriserviceProxy != null && bsrUriserviceProxy.length() !=0){
            	relationshipsElement.appendChild(createRelationshipElement(document, "rest80_RESTProxy", bsrUriserviceProxy));
            } else {
            	relationshipsElement.appendChild(createRelationshipElement(document, "rest80_RESTProxy", null));
            }

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));       

            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/
	
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	
	//11032017 creo nuovo metodo
	public String createZResEndpointXMLDAta(String name,String timeout,String environment,String state,String nomecpy,String sicurezza) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", ""));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","ZRES"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOME_CPY", nomecpy)); 
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_ZRES_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	                    
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));       

            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/
	
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	
	//11032017 creo nuovo metodo
	public String createWolaEndpointXMLDAta(String name,String timeout,String environment,String state,String nomecpy_inp,String nomecpy_out,String sicurezza) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", ""));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","WOLA"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOME_CPY_INP", nomecpy_inp));   
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOME_CPY_OUT", nomecpy_out));  
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_MD", "Y1BP0DLW"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOME_CPY_SIST", "Y1BPMWLA"));
            	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_WOLA_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	                    
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));       

            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/
	
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
	public String createCallableEndpointXMLDAta(String name,String timeout,String environment,String state,String bsrUriserviceProxy,String sicurezza) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "rest80_baseURL", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","REST"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", "X"));
            //040117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
                       
            propertiesElement.appendChild(createPropertyElement(document, "rest80_CALLABLE_ISPHEADER_FLAG", null));
                        
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_CALLABLE_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	        
            if ( bsrUriserviceProxy != null && bsrUriserviceProxy.length() !=0){
            	relationshipsElement.appendChild(createRelationshipElement(document, "rest80_CALLABLEProxy", bsrUriserviceProxy));
            } else {
            	relationshipsElement.appendChild(createRelationshipElement(document, "rest80_CALLABLEProxy", null));
            }

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));       

            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/
	
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
	public String createSoapEndpointXMLDAta(String name,String timeout,String ispheader,String environment,String state,String bsrUriserviceProxy,String sicurezza) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","SOAP"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", "X"));
            //040117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            
            //28/07/2016
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ISPHEADER_FLAG", ispheader));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            //finto mettilo per non andare in errore con modello
            //propertiesElement.appendChild(createPropertyElement(document, "sm63_SOAPProxy", EMPTY_STRING));
	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_SOAP_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_soapAddress", null));
            relationshipsElement.appendChild(createRelationshipElement(document, "sm63_wsdlPorts", null));

            if ( bsrUriserviceProxy != null && bsrUriserviceProxy.length() !=0){
            	//12012017 cambiato prima era rest80..
            	relationshipsElement.appendChild(createRelationshipElement(document, "sm63_SOAPProxy", bsrUriserviceProxy));
            } else {
            	//12012017 cambiato prima era rest80..
            	relationshipsElement.appendChild(createRelationshipElement(document, "sm63_SOAPProxy", null));
            }

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));       

            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/

	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	
	//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
	//21022017 inserita la versione nella creazione di createCicsEndpointXMLDAta
	public String createCicsEndpointXMLDAta(String name,String timeout,String stage,String environment,String state,String sicurezza,String version) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);

	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,version));//21022017
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
              
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType","CICS"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Stage","01")); //default
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", timeout));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
                       
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", "X"));
            //040117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_CICS_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));
            
            /**è stato deciso di non classificare come internal o external
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_INTERNAL_EXTERNAL_STATE + state)));
            **/
            
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	//040117 all'enpoint viene passato il campo sicurezza inserito nella proprieta' : sm63_USO_SICUREZZA
	public String createMqEndpointXMLDAta(String name,String qname,int messLen,String environment,String state,String bsrURIMqManualendpoint,String sicurezza) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);
	        	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name+"_00_MQ_E"));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_DEST", "XICITRE1"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", EMPTY_STRING)); 
            propertiesElement.appendChild(createPropertyElement(document, "sm63_EXPIRY", "0"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_LUNGH_OUT", String.valueOf(messLen)));//
            propertiesElement.appendChild(createPropertyElement(document, "sm63_endpointType", "MQ"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_DEST_RISP",EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLAG_3LINK", "N"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_STATO_OPER","E"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace","X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_QUADRATURA","XIQCTEST"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ID_APPL", "MQPUTNBP"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_TIPO_OPER", "I"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_LUNGH_IN",  String.valueOf(messLen)));//
            propertiesElement.appendChild(createPropertyElement(document, "sm63_TRACCIATURA", "S"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ALTER_COLL", "N"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_TGT_SERVER", name));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PRIORITY", "1"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_FORM", "XIQCTQDH"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_CALL_HEADER", "Q"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_MOD_COLLOQUIO", "A"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_Timeout", "10"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ID_TGT_DES", "MQPUTNBP"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_BACKOUT_COUNT", "3"));
            //040117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_USO_SICUREZZA", sicurezza));
            
            //02/05/2017
        	propertiesElement.appendChild(createPropertyElement(document, "sm63_SPECIALIZZAZIONE",""));
	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_MQ_ENDPOINT));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	        relationshipsElement.appendChild(createRelationshipElement(document, "sm63_mqEndpoint", bsrURIMqManualendpoint));

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));   
            
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}

	public String createMqEndpointManualtXMLDAta(String name,String qname) {
		
	    String output=null;
	
	    try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

	        Document document = docBuilder.newDocument();
	
	        // Resources element
	        Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
	        document.appendChild(resourcesElement);
	
	        // Resource element
	        Element resourceElement = document.createElement(ELEMENT_RESOURCE);
	        resourcesElement.appendChild(resourceElement);
	
	        // Properties element
	        Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
	        resourceElement.appendChild(propertiesElement);
	        
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name+"_00_MQ_E_DESTMQUNICO"));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION,EMPTY_STRING));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceVersion", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_PRIMO_UTILIZZO_MQM", EMPTY_STRING)); 
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATA_ULTIMO_UTILIZZO_MQM", EMPTY_STRING)); 
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PRODOTTO", "XI"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DIR_ID_TGT_DES", "MQPUTNBP"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceName", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_serviceNamespace", "X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_responseQMgr"," "));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_portName","X"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_requestQMgr"," "));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_MOD_COLLOQUIO_MQM", "A"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PROC_DEST", "YYY"));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ID_MACCHINA", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_requestQName", qname));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_responseQName", " "));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_PGM_AREE", "XIC2RQXI"));

	
	        propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_MQ_ENDPOINT_MANUAL));

	        Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
	        resourceElement.appendChild(relationshipsElement);

	        //relationshipsElement.appendChild(createRelationshipElement(document, "sm63_sourceDocument", null));
	        //relationshipsElement.appendChild(createRelationshipElement(document, "sm63_mqEndpoint", null));

            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,"http://isp/#DESTMQUNICO")));       

	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	
	    } catch (Exception e) {
	        e.printStackTrace();
	        output=null;
	    }
	    return output;
	}
	
    public String createServiceLevelDefinitionXMLData(String name,String interfacetype, String bsrURIInterface,TWList data) {

        // Create the variable to return
        String bsrURI = null;
        String output;

        try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_SLD));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, interfacetype));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER_LOCATION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONTEXT_IDENTIFIER_LOCATION, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_SCA_EXPORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_ANONYMOUS_SLA, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CAMPATIBLE_SLDS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_WEB_SERVICE_PORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_REST_SERVICE, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_AVAILABLE_OPERATIONS, null));
            
            relationshipsElement.appendChild(this.createRelationshipElementServiceInterface(document, bsrURIInterface));
            
    		int size = data.getArraySize();
    		for (int i = 0; i < size; i++) {
    			String bsrURIDocument = (String) data.getArrayData(i);
    			 relationshipsElement.appendChild(this.createRelationshipElementEndpoint(document, interfacetype, bsrURIDocument));
    		}
    		
    		if (size==0) {
    			//040117 se interfaccia SCH passo endpoint null
    			relationshipsElement.appendChild(createRelationshipElement(document, "gep63_availableEndpoints", null));
    		}
           
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");

        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }

        return output;
    }
    
    //08032017
    public String createServiceLevelAgreementXMLData(String name,String bsrURISLD,String userdefTime,String designTime) {

        // Create the variable to return
        String bsrURI = null;
        String output;

        try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_SLA ));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, name));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_peakMessageRateDailyDuration", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_DATA_ULTIMO_UTILIZZO_LEGAME_APPL", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_DATA_ULTIMO_UTILIZZO_LEGAME_SYST", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_peakMessageRateDailyTime", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_USERDEFTIME", userdefTime));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_DESIGNTIME", designTime));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_DATA_ULTIMO_UTILIZZO_LEGAME_PROD", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_versionMatchCriteria", "ExactVersion"));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_contextIdentifier", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_RUNTIME", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_maximumMessagesPerDay", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_minimumMessagesPerDay", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_averageMessagesPerDay", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gpx63_peakMessageRate", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_subscriptionTerminationDate", EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, "gep63_subscriptionAvailabilityDate", EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            relationshipsElement.appendChild(createRelationshipElement(document, "gep63_boundSCAimport", null));
            relationshipsElement.appendChild(createRelationshipElement(document, "gep63_agreedEndpoints", bsrURISLD));
            relationshipsElement.appendChild(createRelationshipElement(document, "gep63_serviceLevelPolicies", null));
          
	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");

        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }

        return output;
    }
    public String createServiceLevelDefinitionXMLDataFuffa(String name,String interfacetype, String bsrURIInterface,String bsrURIendpoint) {

        // Create the variable to return
        String bsrURI = null;
        String output;

        try {
	        try {
	            docBuilderFactory = DocumentBuilderFactory.newInstance();
	            docBuilder = docBuilderFactory.newDocumentBuilder();
	
	            XPathFactory xPathFactory = XPathFactory.newInstance();
	            XPath xPath = xPathFactory.newXPath();
	            valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
	        } catch (ParserConfigurationException e) {
	            e.printStackTrace();
	            throw e;
	        } catch (XPathExpressionException e) {
	            e.printStackTrace();
	            throw e;
	        }

            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, name));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_URI_SLD));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONSUMER_IDENTIFIER_LOCATION, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_GEP63_CONTEXT_IDENTIFIER_LOCATION, EMPTY_STRING));

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_SCA_EXPORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_ANONYMOUS_SLA, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CAMPATIBLE_SLDS, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_WEB_SERVICE_PORT, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_BOUND_REST_SERVICE, null));
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_AVAILABLE_OPERATIONS, null));
            
            relationshipsElement.appendChild(this.createRelationshipElementServiceInterface(document, bsrURIInterface));
            relationshipsElement.appendChild(this.createRelationshipElementEndpoint(document, interfacetype, bsrURIendpoint));
    		
            /**
            int size = data.getArraySize();
    		for (int i = 0; i < size; i++) {
    			String bsrURIDocument = (String) data.getArrayData(i);
    			 relationshipsElement.appendChild(this.createRelationshipElementEndpoint(document, interfacetype, bsrURIendpoint));
    		}
            **/   

	        TransformerFactory tf = TransformerFactory.newInstance();
	        Transformer transformer1 = tf.newTransformer();
	        transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
	        StringWriter writer = new StringWriter();
	        transformer1.transform(new DOMSource(document), new StreamResult(writer));
	        output = writer.getBuffer().toString().replaceAll("\n|\r", "");
	        System.out.println(">> "+ output);

        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }

        return output;
    }
    
    //deprecated vedi quella nuova utilizzata per gli envelopes delle librerie/caricamenti
    public String createOrganizationXMLData(String name) {

        String output=null;
        
        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }
        	
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();
            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState ale63_assetType
             * ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             */
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME,name));
            

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_ORGANIZATION));
                     
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_CONTACT, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PROPERTY_ALE63_CONTACT_EMAIL, EMPTY_STRING));
            

            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);

            /*
             * Create elements for each of the required relationships on the BusinessService type, as follows:
             * 
             * ale63_dependency ale63_artifacts ale63_owningOrganization gep63_serviceInterfaceVersions gep63_charter
             */
            relationshipsElement.appendChild(createRelationshipElement(document, RELATIONSHIP_GEP63_CHILD_ORGANIZATIONS, null));
 
            
            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
            /*
             * Process the HTTP response.
             */

        } catch (Exception e) {
            e.printStackTrace();
            output=e.getMessage();
        }
        System.out.println(output);
        System.out.println(".................................................................................................");
        return output;
    }
    
    //18102016
    public  String createServiceProxyEndpointXMLDAta( TWList data,String environment) {
 	
        String output=null;

        try {
            try {
                docBuilderFactory = DocumentBuilderFactory.newInstance();
                docBuilder = docBuilderFactory.newDocumentBuilder();

                XPathFactory xPathFactory = XPathFactory.newInstance();
                XPath xPath = xPathFactory.newXPath();
                valueAttrExpression = xPath.compile(XPATH_EXPR_VALUE_ATTR);
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
                throw e;
            } catch (XPathExpressionException e) {
                e.printStackTrace();
                throw e;
            }
            /*
             * Now create the XML document that represents the BusinessService
             */
            Document document = docBuilder.newDocument();

            // Resources element
            Element resourcesElement = document.createElement(ELEMENT_RESOURCES);
            document.appendChild(resourcesElement);

            // Resource element
            Element resourceElement = document.createElement(ELEMENT_RESOURCE);
            resourcesElement.appendChild(resourceElement);

            // Properties element
            Element propertiesElement = document.createElement(ELEMENT_PROPERTIES);
            resourceElement.appendChild(propertiesElement);

            /*
             * Create elements for each of the required properties on the BusinessService type, as follows:
             * 
             * name namespace version description primaryType ale63_assetWebLink ale63_fullDescription ale63_remoteState
             * ale63_assetType ale63_requirementsLink ale63_ownerEmail ale63_guid ale63_communityName ale63_assetOwners
             * gep63_consumerIdentifier gep63_versionAvailabilityDate gep63_versionTerminationDate
             * 
             * 
             * 
             */
   

            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAME, (String) data.getArrayData(0)));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.NAMESPACE, EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.VERSION,EMPTY_STRING));
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.DESCRIPTION, EMPTY_STRING));
            
            propertiesElement.appendChild(createPropertyElement(document, PropertyConstants.PRIMARY_TYPE, OWL_SERVICEPROXY_ENDPOINT));
            
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ESPOSIZIONE", (String)data.getArrayData(1)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ESPOSTO_INTRANET", (String) data.getArrayData(2)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_RICHIAMABILE_DA_CICS", (String)data.getArrayData(3)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_ESPOSTO_SOCIETA_GRUPPO", (String)data.getArrayData(4)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_ESP_CONTROPARTE_ESTERNA", (String) data.getArrayData(5)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_CONTROPARTE_DSI", (String) data.getArrayData(6)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_CONTROPARTE_INTERNET", (String) data.getArrayData(7)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_SOCIETA_CHE_ESPONE_SERVIZIO", (String) data.getArrayData(8)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_FLG_USO_DATAPOWER_DEDICATO", (String) data.getArrayData(9)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_DATAPOWER_DEDICATO", (String) data.getArrayData(10)));       
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOTE_GEN_WSPROXY", (String) data.getArrayData(11)));
            propertiesElement.appendChild(createPropertyElement(document, "sm63_NOTE", (String) data.getArrayData(12)));
            
            //060117
            propertiesElement.appendChild(createPropertyElement(document, "sm63_ERRORE_GENERAZIONE_WSPROXY", ""));

            //OWL_SERVICEPROXY_ENDPOINT
            
            // Relationships element
            Element relationshipsElement = document.createElement(ELEMENT_RELATIONSHIPS);
            resourceElement.appendChild(relationshipsElement);
            
            Element classificationsElement = document.createElement(ELEMENT_CLASSIFICATIONS);
            resourceElement.appendChild(classificationsElement);
            classificationsElement.appendChild(
            classificationsElement.appendChild(createClassificationElement(document,OWL_ENVIRONMENT_STATE + environment)));  

            TransformerFactory tf = TransformerFactory.newInstance();
            Transformer transformer1 = tf.newTransformer();
            transformer1.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
            StringWriter writer = new StringWriter();
            transformer1.transform(new DOMSource(document), new StreamResult(writer));
            output = writer.getBuffer().toString().replaceAll("\n|\r", "");
 
        } catch (Exception e) {
            e.printStackTrace();
            output=null;
        }
        System.out.println("SHOSTServiceVersion.............................................................................");
        System.out.println(output);
        System.out.println(".................................................................................................");
        
        return output;
    }
    
    public String ISPHeaderFormatter(String bpID, String operation,String user) {
    	//2016-06-12-15.09.44.000755
    	
    	//250717 modifico il formato del TS per aderire alla modifica del toolkit (chiamata Rest)
    	//che ora controlla che il formato del TS sia nella forma: yyyyMMddHHmmssSSSSSS
    	//in tracciatura da quanto detto il formato verra' poi trasformato in: yyyy-MM-dd-HH:mm:ss.SSSSSS
    	
    	//String now=new SimpleDateFormat("yyyy-MM-dd-HH:mm:ss.SSSSSS").format(new Date());
    	String now=new SimpleDateFormat("yyyyMMddHHmmssSSSSSS").format(new Date());
    	
    	String ispHeader="<ISPWebservicesHeader><RequestInfo><TransactionId>%TRANSID%</TransactionId><Timestamp>%TS%</Timestamp><ServiceID>%SERVICEID%</ServiceID><ServiceVersion/></RequestInfo><OperatorInfo UserID=\"%USER%\" IsVirtualUser=\"false\"/><CompanyInfo><ISPCallerCompanyIDCode>01</ISPCallerCompanyIDCode><ISPServiceCompanyIDCode>01</ISPServiceCompanyIDCode></CompanyInfo><BusinessInfo><CustomerID>0</CustomerID></BusinessInfo><TechnicalInfo><ChannelIDCode>WS</ChannelIDCode><ApplicationID>BPM</ApplicationID><CallerServerName>SERVER</CallerServerName><CallerProgramName>BPMPA</CallerProgramName></TechnicalInfo><AdditionalBusinessInfo><Param Name=\"CodUnitaOperativa\" Value=\"14493\"/></AdditionalBusinessInfo></ISPWebservicesHeader>";
        
    	ispHeader=ispHeader.replace("%TRANSID%", bpID);
    	ispHeader=ispHeader.replace("%TS%", now);
    	ispHeader=ispHeader.replace("%SERVICEID%", operation);
    	ispHeader=ispHeader.replace("%USER%", user);
    	
        return ispHeader;
        
    }
}
