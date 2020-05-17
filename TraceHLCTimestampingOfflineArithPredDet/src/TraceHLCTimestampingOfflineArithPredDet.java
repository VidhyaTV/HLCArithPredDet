import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.Locator;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import com.microsoft.z3.*;
import java.nio.file.*;
import java.util.stream.*;
public class TraceHLCTimestampingOfflineArithPredDet {
    static int snapshotcount=0;
    static int flex_window_snapshotcount=0;
    static int fixed_window_snapshotcount=0;
    static int smtPerWindowBasedSnapshotCount=0;
    static int smtPerBatchBasedSnapshotCount=0;
    static String inpfilename="";
    static int debugmode=0;
    static int msgmode=0; //msg distribution mode
    static String clockmode="HLC";
    static float gamma = 0;//value by which right end point of the interval will be extended
	static int intervDropFreq=0;
    static int msgDropFreq=0;
    static String outputLocation = "";
    static String backslash="\\";
    static boolean HLCplusEpsPlusSMT;
    static int batchlength=0;
    static boolean perWindowSMTCheck;
    public static void main(String[] args) {
        try {
            if(args.length < 5) {
                System.out.println("Expected number of arguments: 5. Provided "+args.length);
                System.exit(0);
            }
            debugmode = Integer.parseInt(args[0]); //debugmode==1 is printing mode, debugmode == 2 only prints changepoints and candidates
            msgmode=Integer.parseInt(args[1]); //if 2-different-msg-distr-mode, anything else is normal msg distribution mode..
            //setting gamma
            gamma = Float.parseFloat(args[2]);
            intervDropFreq = Integer.parseInt(args[3]);
            msgDropFreq = Integer.parseInt(args[4]);
            inpfilename = args[5];
            outputLocation = args[6];
            batchlength=10000;
            HLCplusEpsPlusSMT=true;
            perWindowSMTCheck=false;
            File inputFile = new File(inpfilename);
			if(System.getProperty("os.name").toLowerCase().indexOf("win") >= 0){
				backslash="\\";
			} else {
				backslash="/";
			}
            String folderName;
			if(HLCplusEpsPlusSMT){//include gamma in folder name so that a separate folder is created for each gamma setting
                folderName = inpfilename.substring(inpfilename.lastIndexOf('/')+1, inpfilename.lastIndexOf(".xml"))+"_intervDrpFreq"+intervDropFreq+"_msgDrpFreq"+msgDropFreq+"_perWindSMT"+perWindowSMTCheck+"_gamma"+gamma;
            } else { //use same folder for all gamma settings because we can run snapCompare-code to compute false positives for all gamma settings in one run by scanning the single folder
                folderName = inpfilename.substring(inpfilename.lastIndexOf('/')+1, inpfilename.lastIndexOf(".xml"))+"_intervDrpFreq"+intervDropFreq+"_msgDrpFreq"+msgDropFreq;
            }
            outputLocation=outputLocation+backslash+folderName;
            SAXParserFactory factory = SAXParserFactory.newInstance();
            SAXParser saxParser = factory.newSAXParser();//create XML parser instance
            UserHandler userhandler = new UserHandler();
            saxParser.parse(inputFile, userhandler);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
class UserHandler extends DefaultHandler
{
	private Locator locator;
	public void setDocumentLocator( Locator locator )
	{
	this.locator = locator;
	}
    boolean bmsender_time = false;
    boolean bmsgto = false;
    boolean bmsgfrom = false;
    boolean bmreceiver_time = false;
    boolean bstart_time=false;
    boolean bend_time=false;
    boolean bmisc=false;
    int proc_id=-1;//variable to remember process id
    int sender_time=-1;// variable to remember sender time for message RECEIVE
    int senderid=-1;// variable to remember sender id for message RECEIVE
    SysAtHand sysathand=new SysAtHand(); //object that accounts for epsilon and number of processes in current system
	String fromVtoEndStr = TraceHLCTimestampingOfflineArithPredDet.inpfilename.substring(TraceHLCTimestampingOfflineArithPredDet.inpfilename.indexOf("_v")+2, TraceHLCTimestampingOfflineArithPredDet.inpfilename.lastIndexOf(".xml"));
    String intervalLengthStr=fromVtoEndStr.substring(0, Math.max(0,fromVtoEndStr.indexOf('_')));
    Map<Integer, Process> mapofprocesses = new HashMap<Integer, Process>();//map of processes with process id as the key and Process instance as value
    HLC largestIntervalEnd;
    //variables for printing z3 constraints for intervals
    String intervalConstraint="";
    int bracesCount=0;
    String nwfolder=TraceHLCTimestampingOfflineArithPredDet.outputLocation; //input file name without file extension
    int lastProcessedBatchPt=0;
    Set<Integer> ProcsCrossedBatchEnd=new HashSet<Integer>();
    //variable for window based snapshot count for the overall run - including all batches if batch-wise execution was done
    HashSet<Integer> windowsSeen = new HashSet<Integer>();
    //variables for creating common smt constraints for all windows
    String commonConstraintsStr;
    HashSet<String> markedFilesToProcessDuringNxtBatch=new HashSet<String>();//variable to remember file name corresponding to the last window in a batch
    boolean noMoreBatchesToProcessForHLCPlusEps=false;
    boolean noMoreBatchesToProcessForSMTBasedDet=false;
    Vector<Integer> highestPtPerProc = new Vector<Integer>();
    String ExecutionOutputContent="";
    long totatTimeForHLCWithGammaExt=0;
    long totalTimeMarkedWindowsFiltering=0;
    long totalTimeAllWindowsSMT=0;
    long totalTimeMarkedWindowsFilteringWithoutFileWriting=0;
    long totalTimeAllWindowsSMTWithoutFileWriting=0;
    @Override
    public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException
    {
        if (qName.equalsIgnoreCase("message"))
        {
            String type = attributes.getValue("type");
            String process = attributes.getValue("process");
            proc_id=Integer.parseInt(process);
        }
        else if(qName.equalsIgnoreCase("sys"))
        {
            int eps = Integer.parseInt(attributes.getValue("epsilon"));
            int nproc = Integer.parseInt(attributes.getValue("number_of_processes"));
            sysathand.SetEpsilon(eps);
            sysathand.SetNumberOfProcesses(nproc);
            if(TraceHLCTimestampingOfflineArithPredDet.intervDropFreq!=0){
                sysathand.setInterval_length(Integer.parseInt(intervalLengthStr));
            }
            ExecutionOutputContent=ExecutionOutputContent+"\nProcessing "+TraceHLCTimestampingOfflineArithPredDet.inpfilename;
            ExecutionOutputContent=ExecutionOutputContent+"\nfromVtoEndStr:"+fromVtoEndStr;
            ExecutionOutputContent=ExecutionOutputContent+"\nintervalLengthStr:"+intervalLengthStr;
            //setting gamma to epsilon if the provided value is positive
            if(TraceHLCTimestampingOfflineArithPredDet.gamma > 0){
                TraceHLCTimestampingOfflineArithPredDet.gamma = (int)Math.floor(sysathand.GetEpsilon() * TraceHLCTimestampingOfflineArithPredDet.gamma);
            } else {
                //use 0 as gamma value
            }
            //create nproc number of instances of class process and assign ids to them
            for (int i=0; i<nproc; i++){
                Clock nwclock=new Clock();
                if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC")){
                    Vector<Integer> hlcvector=new Vector<Integer>();
                    hlcvector.add(0);
                    hlcvector.add(0);
                    hlcvector.add(0);
                    nwclock=new HLC(hlcvector);
                }
                Process proc = new Process(i,nwclock);
                mapofprocesses.put(i,proc);
                highestPtPerProc.add(0);
            }
            //variable to keep track of the largest know HLC timestamp -- needed to bound
            //epsilon extension of last change-points at processes
            Vector<Integer> tempVector = new Vector<Integer>();
            tempVector.add(0);
            tempVector.add(0);
            tempVector.add(0);
            largestIntervalEnd=new HLC(tempVector);
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                Date smtbefore = new Date();
                String vDeclarationStr="",lDeclarationStr="",epsilonConstraintsStr="",predicateConstraintsStr="(assert ";
                //Creating constraints common to all smt-constraint files
                for (int processId = 0; processId < sysathand.GetNumberOfProcesses(); processId++) {
                    //variable declaration constraints
                    //for each process declare a timestamp variable 'l' and local state variable 'x'
                    vDeclarationStr = vDeclarationStr + "(declare-const x_" + processId + " Bool)\n";
                    lDeclarationStr = lDeclarationStr + "(declare-const l" + processId + " Int)\n";
                    //epsilon constraints
                    for (int pr1 = 0; pr1 < sysathand.GetNumberOfProcesses(); pr1++) {
                        if (pr1 != processId) {
                            epsilonConstraintsStr = epsilonConstraintsStr + "(assert (or (and (<= (- l" + processId + " l" + pr1 + ") " + sysathand.GetEpsilon() + ") (>= (- l" + processId + " l" + pr1 + ") 0)) (and (<= (- l" + pr1 + " l" + processId + ") " + sysathand.GetEpsilon() + ") (>= (- l" + pr1 + " l" + processId + ") 0))))\n";
                        }
                    }
                    //violation/predicate constraints
                    if (processId != sysathand.GetNumberOfProcesses() - 1) {
                        predicateConstraintsStr = predicateConstraintsStr + "(and (= x_" + processId + " true) ";
                    } else {
                        predicateConstraintsStr = predicateConstraintsStr + "(= x_" + processId + " true)";
                    }
                }
                for (int pr = 0; pr < sysathand.GetNumberOfProcesses(); pr++) {
                    predicateConstraintsStr = predicateConstraintsStr + ")";
                }
                predicateConstraintsStr = predicateConstraintsStr + "\n";

                //predicate for mutual exclusion


                commonConstraintsStr = vDeclarationStr+lDeclarationStr+epsilonConstraintsStr+predicateConstraintsStr;
                //Code added for timing
                long marked_smt_diff= ((new Date()).getTime() - smtbefore.getTime());
                //add to all-constraints-in-batch-combined-file
                String allConstraintsInBatchFile= nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "all_constraints_" + lastProcessedBatchPt + "to" +(lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength+sysathand.GetEpsilon())+ ".smt2";
                appendToFile(allConstraintsInBatchFile, commonConstraintsStr);
                long all_smt_diff = ((new Date()).getTime() - smtbefore.getTime());
                totalTimeAllWindowsSMT=totalTimeAllWindowsSMT+all_smt_diff;
                //all other totals consider time without file writing to AllWindowsInOneBatchFile
                totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting+marked_smt_diff;
                totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff;
                totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
            }
        } else if (qName.equalsIgnoreCase("sender_time")) {
            bmsender_time = true;
        } else if (qName.equalsIgnoreCase("to")) {
            bmsgto = true;
        } else if (qName.equalsIgnoreCase("from")) {
            bmsgfrom = true;
        } else if (qName.equalsIgnoreCase("receiver_time")) {
            bmreceiver_time = true;
        } else if (qName.equalsIgnoreCase("interval")) {
            String process = attributes.getValue("process");
            proc_id=Integer.parseInt(process);
        } else if (qName.equalsIgnoreCase("start_time")) {
            bstart_time = true;
        } else if (qName.equalsIgnoreCase("end_time")) {
            bend_time = true;
        } else if (qName.equalsIgnoreCase("associated_variable")) {
            String name = attributes.getValue("name");
            String value = attributes.getValue("value");
            String old_value = attributes.getValue("old_value");
            Process proc= mapofprocesses.get(proc_id);
            //create separate version of clocks for the candidate
            Clock nwclock1, nwclock2;
            if(TraceHLCTimestampingOfflineArithPredDet.clockmode.equals("HLC")) {
                Vector<Integer> hlcvector1=new Vector<Integer>();
                hlcvector1.add(0);
                hlcvector1.add(0);
                hlcvector1.add(0);
                nwclock1=new HLC(hlcvector1);
                //there is guarantee that the old clock should correspond to
                //interval start because no event happens between intervals,
                //the interval start is either end of a false interval or
                //true interval (due to interval split due to communication),
                //either way this value is recorded as old clock value when
                //"endtime" of current interval got processed
                nwclock1.setClock(proc.getProcOldClock().getClock());
                Vector<Integer> hlcvector2=new Vector<Integer>();
                hlcvector2.add(0);
                hlcvector2.add(0);
                hlcvector2.add(0);
                nwclock2=new HLC(hlcvector2);
                nwclock2.setClock(proc.getProcClock().getClock());
                if(highestPtPerProc.elementAt(proc.getId())<proc.getProcClock().getClock().elementAt(0)){
                    highestPtPerProc.setElementAt(proc.getProcClock().getClock().elementAt(0),proc.getId());//index is the set parameter
                }
                //keeping track of the actual clock value of the largest interval end
                if(largestIntervalEnd.lessThan(nwclock2)){
                    largestIntervalEnd.setClock(nwclock2.getClock());
                }
                nwclock2.setClockPlusValue((int)TraceHLCTimestampingOfflineArithPredDet.gamma);
                boolean variableValForIntervalConstraint=false;//to create a false-interval-constraint by default
                if(value.equals("true")) {
                    if(proc.getAcceptInterval()==0|| proc.getProcOldClock().getClock().elementAt(0)-proc.getLastAcceptedStartPt()< sysathand.getInterval_length()){
                        //this was used for an earlier implementation where intervals were
                        //reported as pairs of end-points and intervals during which the value of the local variable "x"
                        //at a process was true were also referred to as true-intervals were reported as "Candidates"
                        //add candidate to process queue
                        proc.newCandidateOccurance(nwclock1,nwclock2);
                        //add change-points to process-queues - current and next appropriately
                        //if right endpoint/changepoint is beyond the end of current batch
                        //and left endpoint/changepoint is within end of current batch
                        proc.newChangePoint(nwclock1,1,1);
                        proc.newChangePoint(nwclock2,-1,1);
                        proc.setLastAcceptedStartPt(proc.getProcOldClock().getClock().elementAt(0));//remember last accepted interval
                        proc.setAcceptInterval(TraceHLCTimestampingOfflineArithPredDet.intervDropFreq);
                        variableValForIntervalConstraint=true;
                    } else{
                        //counting ignored intervals - only if they are far from the previously ignored interval - Solution to interval splits due to communication issue
                        if(proc.getProcOldClock().getClock().elementAt(0)-proc.getLastIgnoredStartPt()> sysathand.getInterval_length()) {
                            proc.setAcceptInterval(proc.getAcceptInterval() - 1);
                            proc.setLastIgnoredStartPt(proc.getProcOldClock().getClock().elementAt(0));//remember last ignored interval
                        }//if current interval is within interval_length of previously ignored interval then its not counted
                    }
                }/* //uncomment the else part below when you have the implementation for processing arithmetic intervals ready
                else{
                    proc.newChangePoint(nwclock1,1,0);
                    proc.newChangePoint(nwclock2,-1,0);
                }
                 */
                //write interval constraints to appropriate file irrespective of whether they are true or false intervals
                if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                    Date smtbefore = new Date();
                    //create constraint
                    String variablename=""+name+"_"+proc_id+"";
                    //make sure to use the actual interval end-timestamps i.e. not the epsilon extended timestamps
                    intervalConstraint=intervalConstraint+"(assert (=> (and (<= "+proc.getProcOldClock().getClock().elementAt(0)+" l"+proc_id+") (< l"+ proc_id +" "+proc.getProcClock().getClock().elementAt(0)+")) (and (= "+variablename+" "+variableValForIntervalConstraint+") ";
                    bracesCount++;
                    long smt_diff = ((new Date()).getTime() - smtbefore.getTime());
                    totalTimeAllWindowsSMT=totalTimeAllWindowsSMT+smt_diff;
                    totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting+smt_diff;
                    totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+smt_diff;
                    totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+smt_diff;
                }
                mapofprocesses.put(proc_id,proc);
            }
        } else if (qName.equalsIgnoreCase("misc")) {
            bmisc = true;
        }
    }

    @Override
    public void endElement(String uri, String localName, String qName) throws SAXException
    {
        if (qName.equalsIgnoreCase("message")) {
        } else if(qName.equalsIgnoreCase("associated_variable")) {
        } else if(qName.equalsIgnoreCase("misc")) {
        } else if(qName.equalsIgnoreCase("interval")) {
            if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                Date smtbefore = new Date();
                Date smtbefore1 = new Date();
                Process proc = mapofprocesses.get(proc_id);
                intervalConstraint = intervalConstraint + " true";
                while (bracesCount > 0) {
                    intervalConstraint = intervalConstraint + ")";
                    bracesCount--;
                }
                intervalConstraint = intervalConstraint + "))\n";
                long all_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeAllWindowsSMT=totalTimeAllWindowsSMT+all_smt_diff;
                totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting+all_smt_diff;
                //Using pattern match find interval Starting and ending Physical time, and associated local-variable-value
                int intervalStartPt=0, intervalEndPt=0;
                String intervStartPatternStr="(.*)(<=\\s)(\\d+)(\\sl)(\\d+)(.*)";
                Pattern pattern1 = Pattern.compile(intervStartPatternStr);
                Matcher matcher1 = pattern1.matcher(intervalConstraint);
                if (matcher1.find()) {
                    intervalStartPt=Integer.parseInt(matcher1.group(3));
                }
                String intervEndPatterStr= "(.*)(<\\sl)(\\d+)(\\s)(\\d+)(.*)";
                Pattern pattern2 = Pattern.compile(intervEndPatterStr);
                Matcher matcher2 = pattern2.matcher(intervalConstraint);
                if (matcher2.find()) {
                    intervalEndPt=Integer.parseInt(matcher2.group(5));
                }
                //compute files/filenames to write to
                //window corresponding to left endpoint/changepoint - windows are defined based on physical time - because snapshots are counted based on physical-time-defined windows
                int lWindow = (proc.getProcOldClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                //window corresponding to right endpoint/changepoint
                int rWindow = (proc.getProcClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                //for each window from lWindow to rWindow
                for (int windowStart = lWindow; windowStart <= rWindow; windowStart = windowStart + sysathand.GetEpsilon()) {
                    //compute the two files corresponding to the window
                    String file1Name, file2Name;
                    //write constraints to both files
                    int startPtInFileNm=windowStart, endPtInFileNm=windowStart + (sysathand.GetEpsilon() * 2);
                    file1Name = "constraints_" + startPtInFileNm + "to" + endPtInFileNm + ".smt2";
                    file1Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file1Name;
                    //interval constraint contains intervalEndPt and intervalStartPt -
                    // ---replace them with max(intervalStart,fileStartPt) and min(intervalEnd,fileEndPt)
                    int updatedStartPt=Math.max(intervalStartPt,startPtInFileNm);
                    int updatedEndPt=Math.min(intervalEndPt,endPtInFileNm);
                    String correctedIntervStr=intervalConstraint.replaceFirst(intervStartPatternStr,"$1$2"+updatedStartPt+"$4$5$6");
                    correctedIntervStr=correctedIntervStr.replaceFirst(intervEndPatterStr,"$1$2$3$4"+updatedEndPt+"$6");
                    long marked_without_file_writing_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                    totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_without_file_writing_smt_diff;
                    appendToFile(file1Name,correctedIntervStr);
                    smtbefore1 = new Date();
                    if (windowStart >= sysathand.GetEpsilon()) {
                        startPtInFileNm=windowStart - sysathand.GetEpsilon();
                        endPtInFileNm=windowStart + sysathand.GetEpsilon();
                        file2Name = "constraints_" + startPtInFileNm + "to" + endPtInFileNm + ".smt2";
                        file2Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + file2Name;
                        updatedStartPt=Math.max(intervalStartPt,startPtInFileNm);
                        updatedEndPt=Math.min(intervalEndPt,endPtInFileNm);
                        correctedIntervStr=intervalConstraint.replaceFirst(intervStartPatternStr,"$1$2"+updatedStartPt+"$4$5$6");
                        correctedIntervStr=correctedIntervStr.replaceFirst(intervEndPatterStr,"$1$2$3$4"+updatedEndPt+"$6");
                        marked_without_file_writing_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                        totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_without_file_writing_smt_diff;
                        appendToFile(file2Name,correctedIntervStr);
                        smtbefore1 = new Date();
                    }
                }
                long marked_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff;
                Date allwind_smtbefore = new Date();//timing writing to all-windows-file
                int currentBatchStrictEnd=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength;
                //add to all-constraints-in-batch-combined-file
                String allConstraintsInBatchFile= nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "all_constraints_" + lastProcessedBatchPt + "to" +(currentBatchStrictEnd+sysathand.GetEpsilon())+ ".smt2";
                appendToFile(allConstraintsInBatchFile, intervalConstraint);
                intervalConstraint = "";
                all_smt_diff = ((new Date()).getTime() - allwind_smtbefore.getTime());
                totalTimeAllWindowsSMT=totalTimeAllWindowsSMT + all_smt_diff;//updating only totalTimeAllWindowsSMT and not totalTimeAllWindowsSMTWithoutFileWriting because this part involves only file writing
                //Check if all processes reached the end of current batch - if yes invoke the chanepoints-processing-function
                if (currentBatchStrictEnd + sysathand.GetEpsilon() < proc.getProcClock().getClock().elementAt(0)) {
                    ProcsCrossedBatchEnd.add(proc_id);
                    if (ProcsCrossedBatchEnd.size() == sysathand.number_of_processes) {
                        EndOfBatchProcessing(false);
                    }
                }
                proc_id = -1;
            }
        } else if(qName.equalsIgnoreCase("system_run")) {
            //Since every batch is processed only when all processes cross batch-boundary = window end + epsilon(i.e.2* epsilon length) there is a pending window(of length epsilon) to be processed
            //also if there are pending marked-smt-files
            while(!noMoreBatchesToProcessForHLCPlusEps || (TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT && (!markedFilesToProcessDuringNxtBatch.isEmpty() || !noMoreBatchesToProcessForSMTBasedDet))) { //noMoreBatchesToProcessForHLCPlusEps is set to true if at least process does not have any more changepoints to process
                EndOfBatchProcessing(true);
            }
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total snapshot count: "+TraceHLCTimestampingOfflineArithPredDet.snapshotcount;
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total time taken for HLC with gamma extension filtering: "+totatTimeForHLCWithGammaExt;
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total time taken for constraint preparation for SMT without gamma filtering"+totalTimeAllWindowsSMTWithoutFileWriting;
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total time taken for constraint preparation and writing for SMT without gamma filtering: "+totalTimeAllWindowsSMT;
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total time taken for constraint preparation for SMT with gamma extension filtering: "+totalTimeMarkedWindowsFilteringWithoutFileWriting;
            ExecutionOutputContent=ExecutionOutputContent+"\nThe total time taken for constraint preparation and writing for SMT with gamma extension filtering: "+totalTimeMarkedWindowsFiltering;
            String outputFileName = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "ExecutionOutput.txt";
            appendToFile(outputFileName,ExecutionOutputContent);
        }
    }
    @Override
    public void characters(char ch[], int start, int length) throws SAXException
    {
        if (bmsender_time) {
            sender_time=Integer.parseInt(new String(ch, start, length));
            bmsender_time = false;
        } else if (bmsgto) {
            int msgto=Integer.parseInt(new String(ch, start, length));
            Process proc= mapofprocesses.get(proc_id);
            if(proc_id!=msgto) {
                proc.updateClockLocalOrSendMsg(sender_time,true);
            } else {
                proc.updateClockLocalOrSendMsg(sender_time,false);//no reporting required for intra-process communication, so logging corresponding l,c values in the queue is not required
            }
            mapofprocesses.put(proc_id,proc);
            proc_id=-1;
            sender_time=-1;
            bmsgto = false;
        } else if (bmsgfrom) {
            senderid=Integer.parseInt(new String(ch, start, length));
            bmsgfrom = false;
        } else if (bmreceiver_time) {
            int receiver_time=Integer.parseInt(new String(ch, start, length));
            //get max of sendertime,receiver_time
            //update clock using that max
            Process proc= mapofprocesses.get(proc_id);
            boolean toss;
			if(TraceHLCTimestampingOfflineArithPredDet.msgmode==2){
                if(proc.getIgnoredMsgCnt()==0){
                    toss=true; //accept the message
                    proc.setIgnoredMsgCnt(TraceHLCTimestampingOfflineArithPredDet.msgDropFreq);
                } else {
                    toss=false; //ignore the message
                    proc.setIgnoredMsgCnt(proc.getIgnoredMsgCnt()-1);
                }
            } else {
                toss=true; // every process receives every message from any other process
            }
            if((proc_id!=senderid) && (toss)) {//based on senderid and on receiver-probability--- if in different msg distribution mode
                //get sender l,c by popping sender's dequeue
                Process senderproc= mapofprocesses.get(senderid);
                MessageSendStruct correspSendClk = senderproc.getClockfromQueue(sender_time);
                proc.updateClockMessageRceive(receiver_time, correspSendClk.getMsgClock());
                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
                if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                    Date smtbefore = new Date();
                    String msgConstraint = ("(assert (=> (>= l" + proc_id + " " + proc.getProcClock().getClock().elementAt(0) + ") (not (< l" + senderid + " " + correspSendClk.getMsgClock().getClock().elementAt(0) + "))))\n");
                    long all_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                    totalTimeAllWindowsSMT=totalTimeAllWindowsSMT+all_smt_diff;
                    totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting+all_smt_diff;
                    //adding it to corresponding window-files
                    HashSet<String> fileNamesToWriteTo=new HashSet<String>();;
                    //find two files in which the receiver pt falls in
                    int windowStart = (proc.getProcClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                    String file1Name = "constraints_" + windowStart + "to" + (windowStart + (sysathand.GetEpsilon() * 2)) + ".smt2";
                    fileNamesToWriteTo.add(file1Name);
                    if (windowStart >= sysathand.GetEpsilon()) {
                        String file2Name = "constraints_" + (windowStart - sysathand.GetEpsilon()) + "to" + (windowStart + sysathand.GetEpsilon()) + ".smt2";
                        fileNamesToWriteTo.add(file2Name);
                    }
                    //find two files in which the sender pt falls in
                    int windowStart1 = (correspSendClk.getMsgClock().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                    String file3Name = "constraints_" + windowStart1 + "to" + (windowStart1 + (sysathand.GetEpsilon() * 2)) + ".smt2";
                    fileNamesToWriteTo.add(file3Name);
                    if (windowStart1 >= sysathand.GetEpsilon()) {
                        String file4Name = "constraints_" + (windowStart1 - sysathand.GetEpsilon()) + "to" + (windowStart1 + sysathand.GetEpsilon()) + ".smt2";
                        fileNamesToWriteTo.add(file4Name);
                    }
                    long marked_without_file_writing_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                    totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_without_file_writing_smt_diff;
                    for(String filename:fileNamesToWriteTo){//add message constraint to each of the identified files
                        appendToFile(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + filename, msgConstraint);
                    }
                    long marked_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                    totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff;
                    Date allwind_smtbefore = new Date();//timing writing to all-windows-file
                    //add to all-constraints-in-batch-combined-file
                    String allConstraintsInBatchFile= "all_constraints_" + lastProcessedBatchPt + "to" +(lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength+sysathand.GetEpsilon())+ ".smt2";
                    appendToFile(nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + allConstraintsInBatchFile, msgConstraint);
                    all_smt_diff = ((new Date()).getTime() - allwind_smtbefore.getTime());
                    totalTimeAllWindowsSMT=totalTimeAllWindowsSMT + all_smt_diff;//updating only totalTimeAllWindowsSMT and not totalTimeAllWindowsSMTWithoutFileWriting because this part involves only file writing
                }
            } else {
                if(proc_id!=senderid) { // case where it chose to ignore msg based on messgeacceptfrequency
                    // to pop corresponding sender info from its queue
                    Process senderproc= mapofprocesses.get(senderid);//get sender l,c by popping sender's dequeue
                    MessageSendStruct correspSendLC = senderproc.getClockfromQueue(sender_time);
                }
                proc.updateClockLocalOrSendMsg(receiver_time,false);
                mapofprocesses.put(proc_id,proc);//update the process instance in the map corresponding the key-process id
            }
            bmreceiver_time = false;
            proc_id=-1;
            sender_time=-1;
            senderid=-1;
        } else if (bstart_time) {
            bstart_time = false;
        } else if (bend_time) {
            int end_time=Integer.parseInt(new String(ch, start, length));
            Process proc= mapofprocesses.get(proc_id);
            //no need to update clocks if bmisc because the clock was already updated at message send/recieve which actually caused this interval end point
            //if(!bmisc)//some intervals marked as "splitduetocommunication" happen to exist in the traces - so update clock for all types of intervals
            {
                proc.updateClockLocalOrSendMsg(end_time,false);
                mapofprocesses.put(proc_id,proc);
            }
            bmisc = false;
            bend_time = false;
        } else if (bmisc) {
        }
    }
    void EndOfBatchProcessing(boolean reachedEOF){
        String csvLogFile=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "timetracking.csv";
        if(lastProcessedBatchPt==0 && TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT){
            appendToFile(csvLogFile,"AWIB: all-windows-in-batch, MWIB: marked-windows-in-batch\nBatch Start PT,run0_AWIB_read_time,run0_AWIB_check_time,run1_AWIB_read_time,run1_AWIB_check_time,run2_AWIB_read_time,run2_AWIB_check_time,run0_MWIB_read_time,run0_MWIB_check_time,run1_MWIB_read_time,run1_MWIB_check_time,run2_MWIB_read_time,run2_MWIB_check_time");
        }
        //HLC plus epsilon based detection
        HashSet<String> markedFilesInBatch=ProcessAndClearCandQueues_HLC();//returns windows/files in batch that had predicate-satisfaction instances
        /***SMT based detection invocation***/
        //Invoke smt solver on file containing constraints from marked file/windows
        if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
            appendToFile(csvLogFile,"\n"+lastProcessedBatchPt+",");
            if(!noMoreBatchesToProcessForSMTBasedDet) {
                //Invoke smt solver on file containing constraints from all windows
                boolean predSatisfactionInBatch = processBatchSMTfile(reachedEOF);
                if (predSatisfactionInBatch) {
                    TraceHLCTimestampingOfflineArithPredDet.smtPerBatchBasedSnapshotCount++;
                    ExecutionOutputContent=ExecutionOutputContent+"\nSMT based per-batch snapshot count so far:" + TraceHLCTimestampingOfflineArithPredDet.smtPerBatchBasedSnapshotCount;
                }
            }
            String smtOutputFile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "SMTCuts.txt";
            int nwSmtCutsCount = processMarkedSMTfiles(markedFilesInBatch, smtOutputFile, reachedEOF);//invoke this function even if filesMarked is empty because any unprocessed marked files from previous batch should be processed
            if(TraceHLCTimestampingOfflineArithPredDet.perWindowSMTCheck){
                TraceHLCTimestampingOfflineArithPredDet.smtPerWindowBasedSnapshotCount=TraceHLCTimestampingOfflineArithPredDet.smtPerWindowBasedSnapshotCount+nwSmtCutsCount;
                ExecutionOutputContent=ExecutionOutputContent+"\nSMT based per-window based snapshot count so far:"+ TraceHLCTimestampingOfflineArithPredDet.smtPerWindowBasedSnapshotCount;
            }
        }
        //clear current changepoint queue and make the next batch's changepoint queue as the current batch's changepoint queue
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++){//loop through all process queues
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            currProc.deepCopyCurrentCPtQueue(currProc.getCPtQueueNextBatch());//make the next batch's queue as the current batch's queue
            currProc.clearNextChangePointQ();//clear next batch's changepoint queue
            mapofprocesses.put(i,currProc);
        }
        int currentBatchStrictEnd=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength;
        ProcsCrossedBatchEnd.clear();
        lastProcessedBatchPt = currentBatchStrictEnd;
        //System.out.println("Processed batch ending in :"+lastProcessedBatchPt+"\n");
        if(TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
            //delete all files created while processing candidates in current batch
            deleteAllButLastFileInCurrentBatch(currentBatchStrictEnd);//lastProcessedBatchPt was updated but we are using currentBatchStrictEnd which is still the same
            Date allwind_smtbefore = new Date();//timing writing to all-windows-file
            Date allwind_smtbefore1 = new Date();//timing writing to all-windows-file without timing file writes
            //preparing next batch's all-constraints file
            String allConstraintsInNxtBatchFile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "all_constraints_" + lastProcessedBatchPt + "to" + (lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength+ sysathand.GetEpsilon()) + ".smt2";
            //identify if there are constraint files in the next batch
            List<String> filesInNextBatch = getConstraintFilesFromBatch(lastProcessedBatchPt);
            if (filesInNextBatch.isEmpty()) {
                ExecutionOutputContent=ExecutionOutputContent+"\nNo more batches for Smt - all windows combined processing";
                noMoreBatchesToProcessForSMTBasedDet = true;
                long all_smt_diff_withoutfilewrites = ((new Date()).getTime() - allwind_smtbefore1.getTime());
                totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting + all_smt_diff_withoutfilewrites;
            } else {
                //if yes copy constraints from all those files to the common-all-constraints file
                long all_smt_diff_withoutfilewrites = ((new Date()).getTime() - allwind_smtbefore1.getTime());
                totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting + all_smt_diff_withoutfilewrites;
                appendToFile(allConstraintsInNxtBatchFile, commonConstraintsStr);//add common constraints- because variable declaration should be first in an smt file
                for (String consfname : filesInNextBatch) {
                    //add constraints from all file in the next batch i.e.files with start pt as lastProcessedBatchPt to start pt as lastProcessedBatchPt+batchlength-epsilon
                    appendContentFromOneFileToAnother(consfname, allConstraintsInNxtBatchFile);
                }
            }
            long all_smt_diff = ((new Date()).getTime() - allwind_smtbefore.getTime());
            totalTimeAllWindowsSMT=totalTimeAllWindowsSMT + all_smt_diff;
        }
    }
    HashSet<String> ProcessAndClearCandQueues_HLC() {
        //variable for window based snapshot count within a batch
        HashSet<String> filesMarked = new HashSet<String>();
        if (sysathand.GetNumberOfProcesses() == 0) {
            System.out.println("Zero processes in system.");
            System.exit(0);
        }
        //get the text between last backslash and .xml
        //For debugging purposes
        /*****************print all candidates and changepoints of all the processes before preprocessing***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode == 1) {
            String snapshot_cand_file = "", snapshot_cpt_file = "";
            if (TraceHLCTimestampingOfflineArithPredDet.gamma == 0) {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
            } else {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "before_candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "before_changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        int strictBatchRt = lastProcessedBatchPt + TraceHLCTimestampingOfflineArithPredDet.batchlength;
        Date before = new Date();//compute time taken for hlc with gamma extension
        for (int i = 0; i < sysathand.GetNumberOfProcesses(); i++) {//loop through all process queues
            Process currProc = mapofprocesses.get(i); //get the current state of the process
            currProc.setCPtQueue(currProc.cleanUpChangePtQ());
            //any pair of changepoint with right changepoint-ohysical-timestamp greater than current window's strict right should be copied to next batch queue
            currProc.fillNextQueueFromCurrentQueue(strictBatchRt);
            if (currProc.getCPtQueueNextBatch().isEmpty()) {
                noMoreBatchesToProcessForHLCPlusEps = true;//last batch
            }
            //currProc.fixLastChangepoint(largestIntervalEnd);
            //remember to update mapofprocesses accordingly
            mapofprocesses.put(i, currProc);
        }
        //compute time taken for hlc with gamma extension
        long r_diff = ((new Date()).getTime() - before.getTime());
        totatTimeForHLCWithGammaExt=totatTimeForHLCWithGammaExt+r_diff;
        //if(noMoreBatchesToProcessForHLCPlusEps){System.out.println("But no more changepoints to process.");}
        /*****************print all candidates and changepoints of all the processes to see if change points were processed correctly***************/
        if (TraceHLCTimestampingOfflineArithPredDet.debugmode == 1) {
            String snapshot_cand_file = "", snapshot_cpt_file = "";
            if (TraceHLCTimestampingOfflineArithPredDet.gamma == 0) {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
            } else {
                snapshot_cand_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "candidates" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                snapshot_cpt_file = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "changepoints" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
            }
            printCandidatesForAllProc(snapshot_cand_file);
            printChangepointsForAllProc(snapshot_cpt_file);
        }
        before = new Date();//compute time taken for hlc with gamma extension
        //create variable overlap_count
        int overlap_count = 0;
        int prevtokenend = 0;
        int minCPtProc = -1;    //process corresponding to the minimum changepoint
        do { //until minCPtProc=-1 at the end of the loop - there is no more unprocessed changepoint to process
            /**********Find minimum among first changepoint in each process' queue*******/
            minCPtProc = findMinCptProc();
            //if at least one process had at least one changepoint to process, then minCPtProc is not -1
            if (minCPtProc != -1) {
                //removing the minimum changepoint from the respective queue and processing it
                Process chosenProc = mapofprocesses.get(minCPtProc);//get the current state of the process
                Deque<ChangePoint> chosenProccPtq = chosenProc.getCPtQueue();//get the changepoint queue of the process
                if (chosenProccPtq.isEmpty()) {
                    ExecutionOutputContent=ExecutionOutputContent+"\nSomething went wrong. Queue at the chosen process is empty.";
                    System.exit(0);
                }
                ChangePoint currentCPt = chosenProccPtq.removeFirst();
                /**************************update overlap count accordingly**************************/
                overlap_count = overlap_count + currentCPt.getEndPointType();
                //remember the effect of clearing the candidate queue of the process
                chosenProc.setCPtQueue(chosenProccPtq);
                //remember to update mapofprocesses accordingly
                mapofprocesses.put(minCPtProc, chosenProc);
                /*************Report timestamp of overlap if it corresponds to a consistent cut****************/
                //if (overlap_count == sysathand.GetNumberOfProcesses()) {
                if (overlap_count == 2) {//check if two processes are accessing the token simultaneously
                    String snapshot_outfile = "", snapshot_flex_window_counted_outfile = "", snapshot_fixed_window_counted_outfile = "";
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                    //********************************creating needed files and folders reporting*******************************
                    if (TraceHLCTimestampingOfflineArithPredDet.gamma == 0) {
                        snapshot_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_clk_" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
                        snapshot_flex_window_counted_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_flex_window_counted_clk" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
                        snapshot_fixed_window_counted_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_fixed_window_counted_clk" + TraceHLCTimestampingOfflineArithPredDet.clockmode + ".txt";
                    } else {
                        snapshot_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_clk_" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                        snapshot_flex_window_counted_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_flex_window_counted_clk" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                        snapshot_fixed_window_counted_outfile = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "snapshots_fixed_window_counted_clk" + TraceHLCTimestampingOfflineArithPredDet.clockmode + "_gamma" + (int) TraceHLCTimestampingOfflineArithPredDet.gamma + ".txt";
                    }
                    //Create folder and files only if it is the first time
                    if (TraceHLCTimestampingOfflineArithPredDet.snapshotcount == 0) { //when the first cut gets detected clean the snapshots file if one already exists
                        fileClearCreateParentDirectory(snapshot_outfile);
                        fileClearCreateParentDirectory(snapshot_flex_window_counted_outfile);
                        fileClearCreateParentDirectory(snapshot_fixed_window_counted_outfile);
                    }
                    //}
                    boolean markifcounted = false;
                    /*********************FLEXIBLE WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    prevtokenend = flexWindowCountSnapshot(currentCPt, prevtokenend, minCPtProc, snapshot_flex_window_counted_outfile);
                    /*********************FIXED WINDOW BASED COUNTING OF SNAPSHOTS**************************/
                    if (fixedWindowCountSnapshot(currentCPt, windowsSeen, minCPtProc, snapshot_fixed_window_counted_outfile)) {//if snapshot was counted as new
                        markifcounted = true;
                        if (TraceHLCTimestampingOfflineArithPredDet.HLCplusEpsPlusSMT) {
                            //mark the smt constraint file for the corresponding window if the snapshot was counted as new
                            //identify corresponding file name
                            int windowStart = (currentCPt.getcPointTimestamp().getClock().elementAt(0) / sysathand.GetEpsilon()) * sysathand.GetEpsilon();
                            //add filename-string to a set-of-strings for the current batch
                            String file1Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "constraints_" + windowStart + "to" + (windowStart + (sysathand.GetEpsilon() * 2)) + ".smt2";
                            filesMarked.add(file1Name);
                            if (windowStart >= sysathand.GetEpsilon()) {
                                //add filename-string to a set-of-strings for the current batch
                                String file2Name = nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "constraints_" + (windowStart - sysathand.GetEpsilon()) + "to" + (windowStart + sysathand.GetEpsilon()) + ".smt2";
                                filesMarked.add(file2Name);
                            }
                        }
                    }
                    //compute time taken for hlc with gamma extension - without time taken to report i.e.write snapshot to file
                    r_diff = ((new Date()).getTime() - before.getTime());
                    totatTimeForHLCWithGammaExt=totatTimeForHLCWithGammaExt+r_diff;
                    /********************writing to all-snapshots file (counted or not)**************************/
                    //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                    reportSnapshot(currentCPt, snapshot_outfile, minCPtProc, markifcounted);
                    //}
                    before = new Date();//compute time taken for hlc with gamma extension
                }//end of if overlap == number of processes
            }//end of if (minCPtProc!=-1)
        } while (minCPtProc != -1);
        ExecutionOutputContent=ExecutionOutputContent+"\nWindow based snapshot count so far using HLC+gamma:" + TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount;
        return filesMarked;
    }

    //Briefly function "processMarkedSMTfiles" performs per-window and per-batch smt based predicate detection
    /***For each marked file:
     * -if it strictly belongs to current batch
     * ----if perWindowSMTCheck is true add necessary constraints to complete the file and invoke solver on it
     * ----add file content to marked-files-combined-file to be run at the end of the batch
     * -if it is a right-side-border file of current batch
     * ----even if perWindowSMTCheck is true do not process it until next batch - because this file may be marked during the next batch for checking
     * ----add file content to marked-files-combined-file to be run at the end of the batch
     * -if it is a left-side-border file of current batch
     * ----if perWindowSMTCheck is true add necessary constraints to complete the file and invoke solver on it - because this was not during previous batch
     * ----do not add file content to marked-files-combined-file - because it was already added during previous batch
     * -if it does not belong to current batch
     * ----just remember to process it later when processing the appropriate batch***/
    /***necessary constraints to complete existing constraint file for per-window processing are:
     * ---common constraints like variable declaration, epsilon constraints, predicate/violation constraints
     * ---interval and message constraints from the existing-marked constraint file,
     * ---upper and lower bound constraints for the timestamp-variable in the file,
     * ---constraint to restrict detection of snapshot which is entirely present in the next window.
     * ---To complete batch-wise-SMT-file: along with above constraints add constraint to avoid detection of snapshot which is entirely present in the next batch***/
    /**At the end of the batch (i.e. end of function) batch-wise smt file is checked for sat/unsat**/
    /**if perWindowSMTCheck is true: The function returns the number of snapshots detected i.e.number of marked smt files that resulted in SAT**/
    int processMarkedSMTfiles(HashSet<String> smtFiles, String smtOutputFile, boolean reachedEOF){
        String csvLogFile=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "timetracking.csv";
        appendToFile(smtOutputFile,"Processing marked files in batch ending at :"+lastProcessedBatchPt+"\n");
        Date smtbefore = new Date();
        Date smtbefore1 = new Date();//for tracking processing of marked files without accounting for time taken for file writes
        for(String unprocessedFile:markedFilesToProcessDuringNxtBatch){//also process any unprocessed files
            smtFiles.add(unprocessedFile);
            long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
            totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
            appendToFile(smtOutputFile,unprocessedFile+" is pending from previous batch.\n");
            smtbefore1 = new Date();
        }
        int smtSnapshotsCount=0;
        // create a single file for all marked windows in the batch and run solver on it at the end of this function
        int currentBatchStrictEnd=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength;
        String markedWindowsCombinedSMTFile= nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash +"combined_constraints_marked_windows" + lastProcessedBatchPt + "to" + (currentBatchStrictEnd+sysathand.GetEpsilon()) + ".smt2";
        //string variable containing constraints to restrict snapshots to marked windows/files when solving all marked-windows/files as a single file
        String combinedBoundConstraintsStr="";
        int windowsProcessedInBatch=0;
        //for each marked file name
        for(String fileNm: smtFiles) {
            /***Determining if file belongs to current batch or (current batch and next batch)**/
            /***because we want to process only files that are complete and not those that will be appended to during the next batch***/
            //fetching window start pt from file name
            int windowSt=0, windowEnd=0;
            Pattern pattern4 = Pattern.compile("(constraints_)(\\d+)(to)(\\d+)(.smt2)");
            Matcher matcher4 = pattern4.matcher(fileNm);
            if (matcher4.find()) {
                windowSt=Integer.parseInt(matcher4.group(2));
                windowEnd=Integer.parseInt(matcher4.group(4));
            }
            //if file is in current batch - strict right end i.e. not including epsilon extension - that file will be processed during the next batch
            if (windowEnd<=currentBatchStrictEnd){
                if(windowsProcessedInBatch==0){//if there is at least one marked file in the batch and if the marked file being processed is the first ever in the batch
                    //if it is a border file from previous batch- do not add it to marked-files-combined-file
                    // ---because it was processed as part of previous batch's marked-files-combined-file
                    if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()) {
                        long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                        totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
                        appendToFile(markedWindowsCombinedSMTFile, commonConstraintsStr);//add common constraints - epsilon constraints, variable declaration, violation/predicate constraint
                        smtbefore1 = new Date();
                    }
                }
                if(markedFilesToProcessDuringNxtBatch.contains(fileNm)) {//remove file from pending files list once you process it
                    markedFilesToProcessDuringNxtBatch.remove(fileNm);
                }
                long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
                long marked_smt_diff_withfilewrites = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff_withfilewrites;
                String newFileNm="";
                /***********Add variable declaration constraints, epsilon constraints, violation/predicate constraints*************/
                //create/update/run file with updated constraints per window only if per-window-smt processing is required
                if(TraceHLCTimestampingOfflineArithPredDet.perWindowSMTCheck) {
                    //new file for the updated constraints
                    newFileNm = fileNm.replace("constraints_", "updatedConstraints_");
                    appendToFile(newFileNm, commonConstraintsStr);//append constraints to new constraints-file
                    //add all constraints(msg and interval constraints) from the current constraint file to the new file
                    appendContentFromOneFileToAnother(fileNm,newFileNm);
                }
                smtbefore = new Date();
                //if it is a border file from previous batch- do not add it to marked-files-combined-file
                if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()) {
                    //add all constraints(msg and interval constraints) from the current constraint file to all-marked-windows-in-batch-combined-file as well
                    appendContentFromOneFileToAnother(fileNm, markedWindowsCombinedSMTFile);
                }
                smtbefore1 = new Date();
                /****************Add timestamp-bound constraints*********************/
                //adding lower and upper bound constraints
                //if you reached end of input file parse last file in batch and get highest timestamps for upperbound
                //invoke file parser to fetch highest timestamps in file - if no interval at some proc set window start as upper bound
                //works because intervals are guaranteed to be split across windows, and no interval means the last interval at the process was present in some previous window and was already processed
                Vector<Integer> highestTimestampsInFile = getHighestTimestamps(reachedEOF,fileNm,windowSt,windowEnd);
                //adding constraint to restrict at least one process' timestamp to be strictly within the current window - [window_start_pt to window_start_pt+epsilon instead of window_start_pt+2*epsilon]
                String boundConstraintsStr="",currentWindowConstraintStr="(assert ";
                //for each process
                for(int pr2=0; pr2 < sysathand.GetNumberOfProcesses(); pr2++){
                    //max(lowest, window start) becomes the lower bound - this forces the timestamp to be picked from the current window
                    boundConstraintsStr = boundConstraintsStr+"(assert (>= l"+pr2+" "+windowSt+"))\n";
                    //any interval that crosses window-end plus epsilon overlap is actually included in the file so this can be used as the timestamp-upper-bound
                    boundConstraintsStr = boundConstraintsStr+"(assert (< l"+pr2+" "+highestTimestampsInFile.elementAt(pr2)+"))\n";
                    //constraint to force that at least one chosen timestamp in the snapshot falls in the current window (i.e. not including epsilon extension)
                    // - this is to avoid snapshots where all points in the snapshot are actually in the next window
                    if(pr2!=sysathand.GetNumberOfProcesses()-1){
                        currentWindowConstraintStr = currentWindowConstraintStr+"(or (< l"+pr2+" "+(windowSt+sysathand.GetEpsilon())+") ";
                        //if it is a border file from previous batch- do not add it to marked-files-combined-file
                        if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()) {
                            //constraint to restrict snapshots to marked windows/files when solving all marked-windows/files as a single file
                            combinedBoundConstraintsStr = combinedBoundConstraintsStr + "(and (and (>= l" + pr2 + " " + windowSt + ") (< l" + pr2 + " " + highestTimestampsInFile.elementAt(pr2) + ")) ";
                        }
                    } else {
                        currentWindowConstraintStr=currentWindowConstraintStr+"(< l"+pr2+" "+(windowSt+sysathand.GetEpsilon())+")";
                        //if it is a border file from previous batch- do not add it to marked-files-combined-file
                        if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()){
                            combinedBoundConstraintsStr = combinedBoundConstraintsStr+"(and (>= l"+pr2+" "+windowSt+") (< l"+pr2+" "+highestTimestampsInFile.elementAt(pr2)+"))";
                        }
                    }
                }
                //adding necessary closing brackets
                for(int pr3=0; pr3 < sysathand.GetNumberOfProcesses(); pr3++) {
                    currentWindowConstraintStr=currentWindowConstraintStr+")";
                    //if it is a border file from previous batch- do not add it to marked-files-combined-file
                    if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()) {
                        if(pr3!=sysathand.GetNumberOfProcesses()-1) {
                            combinedBoundConstraintsStr = combinedBoundConstraintsStr + ")";
                        }
                    }
                }
                currentWindowConstraintStr=currentWindowConstraintStr+"\n";
                //if it is a border file from previous batch- do not add it to marked-files-combined-file
                if(windowSt!=lastProcessedBatchPt-sysathand.GetEpsilon()) {
                    //constraint to restrict snapshot detection to one of the marked windows/files
                    //-otherwise the solver may pick instants from non-marked windows for which we do not include any constraints
                    combinedBoundConstraintsStr = "(or " + combinedBoundConstraintsStr;//adding bounds for the current window/marked file
                    windowsProcessedInBatch++;
                }
                marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
                marked_smt_diff_withfilewrites = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff_withfilewrites;
                //create/update/run file with updated constraints per window only if per-window-smt processing is required
                if(TraceHLCTimestampingOfflineArithPredDet.perWindowSMTCheck) {
                    appendToFile(newFileNm, boundConstraintsStr + currentWindowConstraintStr);
                    //invoke solver on the new-constraints-file - if solver returned SAT then increment the snapshot counter
                    ExecutionOutputContent=ExecutionOutputContent+"\nProcessing:"+newFileNm;
                    if(smt2FileCheck(newFileNm,smtOutputFile,"")){smtSnapshotsCount++;}
                }
                smtbefore = new Date();
                smtbefore1 = new Date();
            } else{//if file in not strictly within current batch
                markedFilesToProcessDuringNxtBatch.add(fileNm);
                //if it is a border file then add it to batch-wise smt processing
                if(windowEnd==currentBatchStrictEnd+sysathand.GetEpsilon()){//if yes - add file's content to marked-files-combined-file
                    long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
                    totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
                    if(windowsProcessedInBatch==0){//if the marked file being processed is the first ever in the batch
                        appendToFile(markedWindowsCombinedSMTFile,commonConstraintsStr);//add common constraints - epsilon constraints, variable declaration, violation/predicate constraint
                    }
                    ExecutionOutputContent=ExecutionOutputContent+"\nAdding to all-marked-windows-combined-file:"+fileNm;
                    //add all constraints(msg and interval constraints) from the current constraint file to all-marked-windows-in-batch-combined-file as well
                    appendContentFromOneFileToAnother(fileNm,markedWindowsCombinedSMTFile);
                    smtbefore1 = new Date();
                    /****************Add timestamp-bound constraints*********************/
                    //if you reached end of input file parse last file in batch and get highest timestamps for upperbound
                    //invoke file parser to fetch highest timestamps in file - if no interval at some proc set window start as upper bound
                    //works because intervals are guaranteed to be split across windows, and no interval means the last interval at the process was present in some previous window and was already processed
                    Vector<Integer> highestTimestampsInFile = getHighestTimestamps(reachedEOF,fileNm,windowSt,windowEnd);
                    //constraint to restrict snapshot detection to one of the marked windows/files
                    //-otherwise the solver may pick instants from non-marked windows for which we do not include any constraints
                    for(int pr6=0; pr6 < sysathand.GetNumberOfProcesses(); pr6++){//for each process
                        if(pr6!=sysathand.GetNumberOfProcesses()-1){
                            combinedBoundConstraintsStr = combinedBoundConstraintsStr+"(and (and (>= l"+pr6+" "+windowSt+") (< l"+pr6+" "+highestTimestampsInFile.elementAt(pr6)+")) ";
                        } else {
                            combinedBoundConstraintsStr = combinedBoundConstraintsStr+"(and (>= l"+pr6+" "+windowSt+") (< l"+pr6+" "+highestTimestampsInFile.elementAt(pr6)+"))";
                        }
                    }
                    for(int pr7=0; pr7 < sysathand.GetNumberOfProcesses()-1; pr7++) {//adding necessary closing brackets
                        combinedBoundConstraintsStr = combinedBoundConstraintsStr + ")";
                    }
                    combinedBoundConstraintsStr="(or "+combinedBoundConstraintsStr;//adding bounds for the current window/marked file
                    windowsProcessedInBatch++;
                }
            }
        }
        /**********Solving batch-based-SMT file
         ********** i.e. invoking solver on a single file (all marked windows/files combined) for the entire batch***/
        /******Updating single-combined-file for all marked windows/files*************/
        if(windowsProcessedInBatch!=0) {
            //adding necessary closing brackets - for all marked-window-bounds combined (or-ing) constraint
            combinedBoundConstraintsStr = combinedBoundConstraintsStr + " false)";
            for (int u = 0; u < windowsProcessedInBatch-1; u++) {
                combinedBoundConstraintsStr = combinedBoundConstraintsStr + ")";
            }
            combinedBoundConstraintsStr = "(assert " + combinedBoundConstraintsStr + ")\n";
            //constraint to find snapshot strictly within the batch
            String lowerBndStr="",closeBrack="",batchBndStr="(assert ";
            for(int pr4=0; pr4 < sysathand.GetNumberOfProcesses(); pr4++){
                //constraint to ensure that all instants in the snapshot start after start of batch
                lowerBndStr=lowerBndStr+"(assert (>= l"+pr4+" "+lastProcessedBatchPt+"))\n";
                if(pr4!=sysathand.GetNumberOfProcesses()-1){
                    //constraint to ensure that at least one instant in the snapshot is within strict end of batch
                    batchBndStr = batchBndStr+"(or (< l"+pr4+" "+currentBatchStrictEnd+") ";
                } else {
                    batchBndStr=batchBndStr+"(< l"+pr4+" "+currentBatchStrictEnd+")";
                }
                closeBrack=closeBrack+")";
            }
            String batchBndConstraintsStr=batchBndStr+closeBrack+"\n"+lowerBndStr;
            combinedBoundConstraintsStr=combinedBoundConstraintsStr+batchBndConstraintsStr;
            long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
            totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
            //run solver on the single file that contains constraints from all marked windows in the batch
            appendToFile(markedWindowsCombinedSMTFile,combinedBoundConstraintsStr);
            ExecutionOutputContent=ExecutionOutputContent+"\nAt the end of batch. Processing "+markedWindowsCombinedSMTFile;
            String smtOutputFileForBatchBasedSolving=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "SMTResultsForBatchBasedSolving.txt";
            if(smt2FileCheck(markedWindowsCombinedSMTFile,smtOutputFileForBatchBasedSolving,csvLogFile) && !TraceHLCTimestampingOfflineArithPredDet.perWindowSMTCheck){smtSnapshotsCount++;}//record output in appropriate file
        } else {
            long marked_smt_diff = ((new Date()).getTime() - smtbefore1.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
            totalTimeMarkedWindowsFilteringWithoutFileWriting=totalTimeMarkedWindowsFilteringWithoutFileWriting+marked_smt_diff;
            appendToFile(csvLogFile,"0,0,0,0,0,0,");//no marked windows in the batch means zero time taken for smt solving
        }
        long marked_smt_diff = ((new Date()).getTime() - smtbefore.getTime());//most of the code after this is relevant to files for marked windows so updating allwindowstimers
        totalTimeMarkedWindowsFiltering=totalTimeMarkedWindowsFiltering+marked_smt_diff;
        return smtSnapshotsCount;
    }
    /**Invoke solver on the current batch's smt file containing constraints of all windows in the batch
    --add upper and lower bound constraints, and constraints to restrict detection to current batch, and then invoke solver*/
    boolean processBatchSMTfile(boolean reachedEOF){/** invoking solver on a single file ( all windows combined) for the entire batch***/
        Date allwind_smtbefore = new Date();//timing writing to all-windows-file
        Date allwind_smtbefore1 = new Date();//timing writing to all-windows-file without timing file writes
        int currentBatchStrictEnd=lastProcessedBatchPt+TraceHLCTimestampingOfflineArithPredDet.batchlength;
        //constraint to find snapshot strictly within the batch
        String lowerBndStr="",closeBrack="",batchBndStr="(assert ";
        for(int pr4=0; pr4 < sysathand.GetNumberOfProcesses(); pr4++){
            //constraint to ensure that all instants in the snapshot start after start of batch
            lowerBndStr=lowerBndStr+"(assert (>= l"+pr4+" "+lastProcessedBatchPt+"))\n";
            if(pr4!=sysathand.GetNumberOfProcesses()-1){
                //constraint to ensure that at least one instant in the snapshot is within strict end of batch
                batchBndStr = batchBndStr+"(or (< l"+pr4+" "+currentBatchStrictEnd+") ";
            } else {
                batchBndStr=batchBndStr+"(< l"+pr4+" "+currentBatchStrictEnd+")";
            }
            closeBrack=closeBrack+")";
        }
        String batchBndConstraintsStr=batchBndStr+closeBrack+"\n"+lowerBndStr;
        String smtOutputFileForBatchBasedSolving=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "SMTResultsForBatchBasedSolving.txt";
        String csvLogFile=nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash+ "timetracking.csv";
        /******Updating single-combined-file for all windows/files******/
        String allConstraintsInBatchFile= nwfolder + TraceHLCTimestampingOfflineArithPredDet.backslash + "all_constraints_" + lastProcessedBatchPt + "to" +(currentBatchStrictEnd+sysathand.GetEpsilon())+ ".smt2";
        //add constraints to find snapshot strictly within the batch - i.e. at least one instant in the snapshot is within the batch
        long all_smt_diff_withoutfilewrites = ((new Date()).getTime() - allwind_smtbefore1.getTime());
        totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting + all_smt_diff_withoutfilewrites;
        appendToFile(allConstraintsInBatchFile,batchBndConstraintsStr);
        allwind_smtbefore1 = new Date();
        /**add  upper bounds**/ //these were not required for marked-files-combined because we included the window-bound constraints of all marked-windows/files as it is
        //if you reached end of input file parse last file in batch and get highest timestamps for upperbound
        String perProcUpperBndStr="";
        for(int pr5=0; pr5 < sysathand.GetNumberOfProcesses(); pr5++) {
            perProcUpperBndStr = perProcUpperBndStr + "(assert (< l" + pr5 + " " + (Math.min(currentBatchStrictEnd+sysathand.GetEpsilon(),highestPtPerProc.elementAt(pr5))) + "))\n";
        }
        all_smt_diff_withoutfilewrites = ((new Date()).getTime() - allwind_smtbefore1.getTime());
        totalTimeAllWindowsSMTWithoutFileWriting=totalTimeAllWindowsSMTWithoutFileWriting + all_smt_diff_withoutfilewrites;
        appendToFile(allConstraintsInBatchFile,perProcUpperBndStr);
        long all_smt_diff = ((new Date()).getTime() - allwind_smtbefore.getTime());
        totalTimeAllWindowsSMT=totalTimeAllWindowsSMT + all_smt_diff;//updating only totalTimeAllWindowsSMT and not totalTimeAllWindowsSMTWithoutFileWriting because this part involves only file writing
        ExecutionOutputContent=ExecutionOutputContent+"\nAt the end of batch. Processing "+allConstraintsInBatchFile;
        return smt2FileCheck(allConstraintsInBatchFile,smtOutputFileForBatchBasedSolving,csvLogFile);
    }
    //Function smt2FileCheck is from the below GITHUB repository
    /***************************************************************************************
     *    Title: Z3Prover
     *    Availability: https://github.com/Z3Prover/z3/blob/b7a27ca4bd25792208a77dae7e6023fce2a01291/examples/java/JavaExample.java
     ***************************************************************************************/
    boolean smt2FileCheck(String filename, String smtOutputFile, String csvLogFile) {
        boolean sat=false;
        String smtOutputStr="Processing "+filename+"\n";
        String csvOut="";
        int i=0;
        while(i<3) {
            Date before = new Date();
            System.gc();
            HashMap<String, String> cfg = new HashMap<String, String>();
            cfg.put("model", "true");
            Context ctx = new Context(cfg);
            BoolExpr a = ctx.mkAnd(ctx.parseSMTLIB2File(filename, null, null, null, null));
            long r_diff = ((new Date()).getTime() - before.getTime());
            Solver solver1 = ctx.mkSimpleSolver();
            solver1.add(a);
            Status result1 = solver1.check();
            long t_diff = ((new Date()).getTime() - before.getTime());
            csvOut=csvOut+r_diff+","+t_diff+",";
            smtOutputStr=smtOutputStr+"SMT2 file read time: " + r_diff + " millisec\n";
            smtOutputStr = smtOutputStr + "Model check result  " + result1 + "\n";
            smtOutputStr = smtOutputStr + "SMT2 file check took " + t_diff + " millisec\n";
            //Statistics stat = solver1.getStatistics();
            //smtOutputStr = smtOutputStr + stat.toString() + "\n";
            if (result1.equals(Status.SATISFIABLE)) {
                final Model model = solver1.getModel();
                for (FuncDecl constExpr : model.getConstDecls()) {//get interpretation of all consts in the model
                    smtOutputStr = smtOutputStr + constExpr.getName() + ":" + model.getConstInterp(constExpr) + "\n";
                }
                sat = true;
            }
            i++;
        }
        //record the SAT mode obtained
        if(csvLogFile!=""){appendToFile(csvLogFile, csvOut);}
        appendToFile(smtOutputFile, smtOutputStr);
        return sat;
    }
    void deleteFileIfExists(String fullFileName){
        try {
            Files.deleteIfExists(Paths.get(fullFileName));
        }
        catch(NoSuchFileException e) {
            System.out.println("Delete Failed. No such file/directory exists");
        }
        catch(DirectoryNotEmptyException e) {
            System.out.println("Delete Failed. Directory is not empty.");
        }
        catch(IOException e) {
            System.out.println("Delete Failed. Invalid permissions.");
        }
    }
    List<String> getListOfFilesInLoc(String folderName, String endsWith){
        List<String> result= new ArrayList<>();
        File tmpDir = new File(folderName);
        if(tmpDir.exists()) {
            try {
                result = Files.walk(Paths.get(folderName)).map(x -> x.toString()).filter(f -> f.endsWith(endsWith)).collect(Collectors.toList());
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return result;
    }
    Vector<Integer> getHighestTimestamps(boolean reachedEOF, String fileNm, int defaultValToFillInVec, int windowEndPt) {
        Vector<Integer> highestTimestamps = new Vector<Integer>();
        if(!reachedEOF){
            for(int processId=0; processId<sysathand.GetNumberOfProcesses(); processId++){
                highestTimestamps.add(windowEndPt);
            }
        } else {
            for (int processId = 0; processId < sysathand.GetNumberOfProcesses(); processId++) {
                highestTimestamps.add(defaultValToFillInVec);//will be used if there are no intervals in the file for some process
            }
            try {
                BufferedReader reader = new BufferedReader(new FileReader(fileNm));
                String line = reader.readLine();
                while (line != null) {//for each line in the existing constraint file
                    //identifying highest timestamps for each process to specify upper bounds constraints
                    Pattern pattern2 = Pattern.compile("(.*)(<\\sl)(\\d+)(\\s)(\\d+)(.*)");//get last instance of this pattern in the file for each process
                    Matcher matcher2 = pattern2.matcher(line);
                    if (matcher2.find() && !line.contains("not")) {
                        highestTimestamps.setElementAt(Integer.parseInt(matcher2.group(5)), Integer.parseInt(matcher2.group(3)));//index is the second parameter
                    }
                    // read next line
                    line = reader.readLine();
                }
                reader.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return highestTimestamps;
    }
    boolean allNonZeroTimestamps(Vector<Integer> timestampsVec){
        if(timestampsVec.isEmpty()){return false;}
        for(int processId=0; processId<sysathand.GetNumberOfProcesses(); processId++){
            if(timestampsVec.elementAt(processId)==0){return false;}
        }
        return true;
    }
    void appendContentFromOneFileToAnother(String fileNm, String newFileNm){
        try {
            BufferedReader reader = new BufferedReader(new FileReader(fileNm));
            BufferedWriter writer = new BufferedWriter(new FileWriter(newFileNm, true));//true for append
            String line = reader.readLine();
            while (line != null) {//for each line in the existing  file
                writer.write(line + "\n");
                // read next line
                line = reader.readLine();
            }
            writer.close();
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
    int getWindow(int cPtLvalue, int syseps) {
        int window=cPtLvalue/syseps;
        return window;
    }
    int findMinCptProc() {
        int minCPtProc=-1; //set to default value beginning
        Vector<Integer> temp= new Vector<Integer>();
        temp.add(0);
        temp.add(0);
        temp.add(0);
        //variable for finding and storing minimum changepoint
        ChangePoint minCPt= new ChangePoint(new HLC(temp),0,-1);
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process otherProc= mapofprocesses.get(i); //get the current state of the process
            Deque<ChangePoint> otherProccPtq=otherProc.getCPtQueue();//get the changepoint queue of the process
            if (!otherProccPtq.isEmpty())//if there is at least one unprocessed changepoint
            {
                ChangePoint cPt = otherProccPtq.getFirst();//get current first changepoint in queue
                if (minCPtProc==-1) //default value is -1,
                {
                    minCPt=cPt;	//setting the changepoint from the first process as minimum to start with
                    minCPtProc=i;
                }
                else{
                    int minl=minCPt.getcPointTimestamp().getClock().get(1);
                    int minc=minCPt.getcPointTimestamp().getClock().get(2);
                    int minPtType=minCPt.getEndPointType();
                    int currentl=cPt.getcPointTimestamp().getClock().get(1);
                    int currentc=cPt.getcPointTimestamp().getClock().get(2);
                    int currentPtType=cPt.getEndPointType();
                    //compare l and c values of all the smallest changepoints across processes
                    // if l and c values are equal then right endpoints have higher priority than left endpoints - i.e. they should be processed first
                    if (((currentl== minl)&&(currentc== minc)&&(currentPtType<minPtType)) || ((currentl< minl) || ((currentl== minl)&&(currentc< minc))))
                    {
                        minCPt=cPt;
                        minCPtProc=i;
                    }
                }
            }
        }
        return minCPtProc;
    }
    void printCandidatesForAllProc(String filename){
        File tmpDir = new File(filename);
        boolean exists = tmpDir.exists();
        if(!exists){
            fileClearCreateParentDirectory(filename);
        }
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCandQueueToFile(filename);
        }
    }
    void printChangepointsForAllProc(String filename){
        File tmpDir = new File(filename);
        boolean exists = tmpDir.exists();
        if(!exists){
            fileClearCreateParentDirectory(filename);
        }
        for(int i=0;i<sysathand.GetNumberOfProcesses();i++)//loop through all process queues
        {
            Process currProc= mapofprocesses.get(i); //get the current state of the process
            //since same file is passed for all processes -delete before a run because it is set to open in append mode
            currProc.printCPtQueueToFile(filename);
        }
    }
    void fileClearCreateParentDirectory(String filename){
        try{//clear current contents of the file
            File ifilename = new File(filename);
            ifilename.getParentFile().mkdirs();//create necessary parent directory
            new PrintWriter(filename).close();//clear current contents of the file
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
    int flexWindowCountSnapshot(ChangePoint currentCPt, int prevtokenend, int minCPtProc, String filename){
        /********Counting the snapshot only if it is epsilon away from previously detected snapshot********/
        int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        //if current overlap's i.e.changepoints' start-l is epsilon away from the previous overlap's start-l
        if((cPtLvalue-prevtokenend>sysathand.GetEpsilon()) || (TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount==0)){
            TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount++;
            //get/save the overlap's ending pt
            prevtokenend=cPtLvalue;
            /**********writing to snapshot_counted_outfile*******************/
            if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1) {
                writeSnapshotToFile(minCPtProc, currentCPt, filename,TraceHLCTimestampingOfflineArithPredDet.flex_window_snapshotcount);
            }
        }
        return prevtokenend;
    }
    boolean fixedWindowCountSnapshot(ChangePoint currentCPt,HashSet<Integer> windowsSeen, int minCPtProc, String filename){
        /***Counting the snapshot only if its current-epsilon-based window is different from the previously detected snapshot********/
        //int cPtLvalue = currentCPt.getcPointTimestamp().getClock().get(1);
        int cPtvalue = currentCPt.getcPointTimestamp().getClock().get(0);
        //compute the current cut's window based on epsilon
        int current_cut_window=getWindow(cPtvalue,sysathand.GetEpsilon());
        if((TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount==0)||(!windowsSeen.contains(current_cut_window)))
        {
            TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount++;
            windowsSeen.add(current_cut_window);
            //if (TraceHLCTimestampingOfflineArithPredDet.debugmode==1)
            {
                /***************writing to snapshot_window_counted_outfile************************/
                writeSnapshotToFile(minCPtProc,currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.fixed_window_snapshotcount);
            }
            return true;
        }
        return false;
    }
    void reportSnapshot(ChangePoint currentCPt, String filename, int minCPtProc, boolean markifcounted){
        TraceHLCTimestampingOfflineArithPredDet.snapshotcount++;
        writeSnapshotToFile(minCPtProc, currentCPt,filename,TraceHLCTimestampingOfflineArithPredDet.snapshotcount);
        if(markifcounted) {
            appendToFile(filename," Was Counted");
        }
    }
    void writeSnapshotToFile(int minCPtProc, ChangePoint currentCPt, String filename, int snapshotCount){
        try {
            BufferedWriter bw2 = new BufferedWriter(new FileWriter(filename, true));//true for append
            bw2.write("\n At Process"+minCPtProc+" Snapshot No:"+snapshotCount+"-->");
            bw2.write("[P"+minCPtProc+":<"+currentCPt.getcPointTimestamp().getClock().get(0)+",<"+currentCPt.getcPointTimestamp().getClock().get(1)+","+currentCPt.getcPointTimestamp().getClock().get(2)+">>");
            bw2.close();
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
    }
    void appendToFile(String filename, String text){
        try{
            File tmpDir = new File(filename);
            boolean exists = tmpDir.exists();
            if(!exists){
                fileClearCreateParentDirectory(filename);
            }
            BufferedWriter bw1=new BufferedWriter(new FileWriter(filename, true));//true for append
            bw1.write(text);
            bw1.close();
        } catch (IOException ioe){
            ioe.printStackTrace();
        }
    }
    //deletes all files in current batch except last file i.e. the border file
    //also deletes any file from the previous batch's processing
    void deleteAllButLastFileInCurrentBatch(int batchStrictBorder){
        //list constraint files in the output folder i.e.those that contain ".smt2" in name
        List<String> constraintFilesInFolder=getListOfFilesInLoc(nwfolder, ".smt2");
        //for each of these files if the file name contains "to"+number s.t. number<=batchStrictBorder then delete the file
        for (String file : constraintFilesInFolder) {
            //get window-end pt from file name
            int windowEnd = Integer.parseInt(file.substring(file.lastIndexOf("to")+2,file.indexOf(".smt2")));
            //if file is within current batch
            if(windowEnd<=batchStrictBorder){
                //delete it
                deleteFileIfExists(file);
            }
        }
    }
    //identify if there are constraint files in the next batch
    List<String> getConstraintFilesFromBatch(int batchStartPt){
        List<String> constraintFilesInFolder= getListOfFilesInLoc(nwfolder,".smt2");
        List<String> filesInBatch=new ArrayList<>();
        int lastPossFileEndPt=batchStartPt+TraceHLCTimestampingOfflineArithPredDet.batchlength+sysathand.GetEpsilon();
        //for each of these files if the file name contains "to"+number s.t. number<=batchStrictBorder then delete the file
        for (String fileN : constraintFilesInFolder) {
            if(fileN.contains(TraceHLCTimestampingOfflineArithPredDet.backslash+"constraints_")) {
                //get window-start pt from file name
                int windowStart = Integer.parseInt(fileN.substring(fileN.lastIndexOf("_") + 1, fileN.lastIndexOf("to")));
                int windowEnd = Integer.parseInt(fileN.substring(fileN.lastIndexOf("to") + 2, fileN.indexOf(".smt2")));
                //if file is within current batch
                if (windowStart >= batchStartPt && windowEnd <= lastPossFileEndPt) {
                    //add to list
                    filesInBatch.add(fileN);
                }
            }
        }
        return filesInBatch;
    }
}